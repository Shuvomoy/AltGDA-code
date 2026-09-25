import Mathlib

   
                                    

                                                                              
                                                                           
                             
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

abbrev EVec (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

abbrev PayoffOperator (ι κ : Type*) [Fintype ι] [Fintype κ] :=
  EVec ι →L[ℝ] EVec κ

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

def ones (ι : Type*) [Fintype ι] : EVec ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun _ => 1)

@[simp]
theorem ones_apply (i : ι) : ones ι i = 1 := by
  rfl

end


end AltGDA
