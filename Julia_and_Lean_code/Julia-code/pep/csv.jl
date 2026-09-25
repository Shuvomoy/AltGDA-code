
import JLD2
import SHA

"""Return an RFC-4180-style representation of one CSV field."""
function csv_escape(value)::String
    value === missing && return ""
    value === nothing && return ""

    field = string(value)
    if any(character -> character in (',', '"', '\r', '\n'), field)
        return '"' * replace(field, "\"" => "\"\"") * '"'
    end
    return field
end

function _parse_csv_records(contents::String)::Vector{Vector{String}}
    characters = collect(contents)
    records = Vector{Vector{String}}()
    record = String[]
    field = IOBuffer()
    state = :unquoted
    pending_record = false

    index = 1
    while index <= length(characters)
        character = characters[index]

        if state === :quoted
            if character == '"'
                if index < length(characters) && characters[index + 1] == '"'
                    write(field, '"')
                    index += 1
                else
                    state = :after_quote
                end
            else
                write(field, character)
            end
        elseif state === :after_quote
            if character == ','
                push!(record, String(take!(field)))
                state = :unquoted
                pending_record = true
            elseif character == '\r' || character == '\n'
                push!(record, String(take!(field)))
                push!(records, record)
                record = String[]
                state = :unquoted
                pending_record = false
                if character == '\r' && index < length(characters) && characters[index + 1] == '\n'
                    index += 1
                end
            else
                throw(ArgumentError("unexpected character after a closing CSV quote"))
            end
        else
            if character == '"'
                position(field) == 0 || throw(ArgumentError("CSV quote must begin at the start of a field"))
                state = :quoted
                pending_record = true
            elseif character == ','
                push!(record, String(take!(field)))
                pending_record = true
            elseif character == '\r' || character == '\n'
                push!(record, String(take!(field)))
                push!(records, record)
                record = String[]
                pending_record = false
                if character == '\r' && index < length(characters) && characters[index + 1] == '\n'
                    index += 1
                end
            else
                write(field, character)
                pending_record = true
            end
        end

        index += 1
    end

    state === :quoted && throw(ArgumentError("unterminated quoted CSV field"))
    if pending_record
        push!(record, String(take!(field)))
        push!(records, record)
    end
    return records
end

"""
    read_simple_csv(path) -> Vector{Dict{String,String}}

Read a header-based CSV file without loading CSV.jl or DataFrames.jl. Quoted
fields, doubled quotes, CRLF input, and newlines inside quoted fields are
supported. Every data row must have exactly the header width.
"""
function read_simple_csv(path::AbstractString)::Vector{Dict{String,String}}
    isfile(path) || throw(ArgumentError("CSV file does not exist: $(path)"))
    records = _parse_csv_records(read(path, String))
    isempty(records) && return Dict{String,String}[]

    header = copy(first(records))
    if !isempty(header) && !isempty(header[1]) && first(header[1]) == '\ufeff'
        header[1] = chop(header[1]; head = 1, tail = 0)
    end
    isempty(header) && throw(ArgumentError("CSV header must not be empty"))
    any(isempty, header) && throw(ArgumentError("CSV header names must not be empty"))
    length(unique(header)) == length(header) || throw(ArgumentError("CSV header names must be unique"))

    rows = Vector{Dict{String,String}}()
    for (record_index, values) in enumerate(Iterators.drop(records, 1))
        length(values) == length(header) || throw(ArgumentError(
            "CSV record $(record_index + 1) has $(length(values)) fields; expected $(length(header))",
        ))
        push!(rows, Dict(header[column] => values[column] for column in eachindex(header)))
    end
    return rows
end

function _row_values(row, header::Vector{String})
    if row isa NamedTuple
        values = Any[]
        for name in header
            key = Symbol(name)
            haskey(row, key) || throw(ArgumentError("CSV row is missing column $(repr(name))"))
            push!(values, row[key])
        end
        return values
    elseif row isa AbstractDict
        values = Any[]
        for name in header
            if haskey(row, name)
                push!(values, row[name])
            elseif haskey(row, Symbol(name))
                push!(values, row[Symbol(name)])
            else
                throw(ArgumentError("CSV row is missing column $(repr(name))"))
            end
        end
        return values
    elseif row isa Tuple || (row isa AbstractVector && !(row isa AbstractString))
        length(row) == length(header) || throw(ArgumentError(
            "CSV row has $(length(row)) fields; expected $(length(header))",
        ))
        return collect(row)
    end
    throw(ArgumentError("CSV rows must be dictionaries, named tuples, tuples, or vectors"))
end

function _atomic_destination(writer::Function, path::AbstractString)::String
    isempty(path) && throw(ArgumentError("destination path must not be empty"))
    destination = abspath(normpath(path))
    destination_directory = dirname(destination)
    mkpath(destination_directory)

    temporary_path, temporary_io = mktemp(destination_directory; cleanup = false)
    close(temporary_io)
    try
        writer(temporary_path)
        isfile(temporary_path) || error("atomic writer did not create its temporary file")
        mv(temporary_path, destination; force = true)
    finally
        ispath(temporary_path) && rm(temporary_path; force = true)
    end
    return destination
end

"""
    write_csv_atomic(path, header, rows) -> String

Write `rows` using `header`, then replace `path` only after the complete CSV
has been closed in the destination directory. Rows may be dictionaries, named
tuples, tuples, or vectors. The returned path is absolute.
"""
function write_csv_atomic(path::AbstractString, header, rows)::String
    column_names = string.(collect(header))
    isempty(column_names) && throw(ArgumentError("CSV header must not be empty"))
    any(isempty, column_names) && throw(ArgumentError("CSV header names must not be empty"))
    length(unique(column_names)) == length(column_names) || throw(ArgumentError("CSV header names must be unique"))

    return _atomic_destination(path) do temporary_path
        open(temporary_path, "w") do io
            write(io, join(csv_escape.(column_names), ','), '\n')
            for row in rows
                values = _row_values(row, column_names)
                write(io, join(csv_escape.(values), ','), '\n')
            end
        end
    end
end

function _require_jld_suffix(path::AbstractString)
    lowercase(splitext(path)[2]) == ".jld" || throw(ArgumentError(
        "JLD2 checkpoints must use the roadmap-compatible .jld suffix: $(path)",
    ))
    return nothing
end

"""
    save_jld_atomic(path; kwargs...) -> String

Save each keyword as a top-level JLD2 dataset. The file intentionally uses the
roadmap-compatible `.jld` suffix, although its format is JLD2 rather than the
legacy JLD package. The returned path is absolute.
"""
function save_jld_atomic(path::AbstractString; kwargs...)::String
    _require_jld_suffix(path)
    isempty(kwargs) && throw(ArgumentError("a checkpoint must contain at least one named value"))

    return _atomic_destination(path) do temporary_path
        JLD2.jldopen(temporary_path, "w") do file
            for (name, value) in pairs(kwargs)
                file[string(name)] = value
            end
        end

        payload = JLD2.load(temporary_path)
        for name in keys(kwargs)
            haskey(payload, string(name)) || error("JLD2 checkpoint validation failed for key $(name)")
        end
    end
end

"""Load and return all top-level values from a JLD2 checkpoint named `.jld`."""
function load_jld(path::AbstractString)::Dict{String,Any}
    _require_jld_suffix(path)
    isfile(path) || throw(ArgumentError("JLD2 checkpoint does not exist: $(path)"))
    payload = JLD2.load(path)
    return Dict{String,Any}(string(name) => value for (name, value) in pairs(payload))
end

function _sha256_file(path::AbstractString)
    return open(path, "r") do io
        SHA.sha256(io)
    end
end

"""
    promote_file(source, destination) -> String

Copy a completed scratch artifact into the destination directory, verify that
the copy is byte-for-byte identical using its size and SHA-256 digest, and only
then atomically replace `destination`. The scratch file is retained.
"""
function promote_file(source::AbstractString, destination::AbstractString)::String
    isfile(source) || throw(ArgumentError("promotion source does not exist: $(source)"))
    source_path = abspath(normpath(source))
    destination_path = abspath(normpath(destination))
    source_path == destination_path && return destination_path

    source_size = filesize(source_path)
    source_digest = _sha256_file(source_path)
    promoted_path = _atomic_destination(destination_path) do temporary_path
        cp(source_path, temporary_path; force = true)
        filesize(temporary_path) == source_size || error("promoted artifact size differs from its scratch source")
        _sha256_file(temporary_path) == source_digest || error("promoted artifact digest differs from its scratch source")
        filesize(source_path) == source_size || error("scratch artifact changed during promotion")
        _sha256_file(source_path) == source_digest || error("scratch artifact changed during promotion")
    end
    return promoted_path
end
