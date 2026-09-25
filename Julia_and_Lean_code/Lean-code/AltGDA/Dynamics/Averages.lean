import AltGDA.Dynamics.AltGDA

   
                                        
  

open scoped BigOperators

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

theorem avgX_mem (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (T : ℕ) (hT : 0 < T) :
    avgX A η s0 T ∈ simplex ι := by
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  simpa [avgX] using
    (simplex_uniformAverage_mem
      (x := fun t : Fin T ↦ xIter A η s0 (t.1 + 1))
      (fun t ↦ xIter_mem A η s0 (t.1 + 1)))

theorem avgY_mem (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (T : ℕ) (hT : 0 < T) :
    avgY A η s0 T ∈ simplex κ := by
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  simpa [avgY] using
    (simplex_uniformAverage_mem
      (x := fun t : Fin T ↦ yIter A η s0 (t.1 + 1))
      (fun t ↦ yIter_mem A η s0 (t.1 + 1)))

end


end AltGDA
