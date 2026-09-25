import AltGDA.Prelude

   
                            

                                                                       
                                                                       
                                                                      
                 
  

open scoped InnerProduct

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                        
abbrev payoffAdjoint (A : PayoffOperator ι κ) : PayoffOperator κ ι := A†

                                                                      
def matrixOperator (M : Matrix κ ι ℝ) : PayoffOperator ι κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦
        (WithLp.equiv 2 (κ → ℝ)).symm (fun j ↦ ∑ i, M j i * x i)
      map_add' := by
        intro x z
        ext j
        change (∑ i, M j i * (x i + z i)) =
          (∑ i, M j i * x i) + ∑ i, M j i * z i
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      map_smul' := by
        intro a x
        ext j
        change (∑ i, M j i * (a * x i)) = a * ∑ i, M j i * x i
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }

@[simp]
theorem matrixOperator_apply (M : Matrix κ ι ℝ) (x : EVec ι) (j : κ) :
    matrixOperator M x j = ∑ i, M j i * x i := by
  rfl

                                                                                    
@[simp]
theorem matrixOperator_adjoint (M : Matrix κ ι ℝ) :
    payoffAdjoint (matrixOperator M) = matrixOperator M.transpose := by
  ext y i
  have h := ContinuousLinearMap.adjoint_inner_right (matrixOperator M)
    (EuclideanSpace.single i (1 : ℝ)) y
  simpa [PiLp.inner_apply, PiLp.single_apply, Matrix.transpose_apply,
    mul_comm] using h

@[simp]
theorem matrixOperator_adjoint_apply (M : Matrix κ ι ℝ) (y : EVec κ) (i : ι) :
    payoffAdjoint (matrixOperator M) y i = ∑ j, M j i * y j := by
  rw [matrixOperator_adjoint]
  simp [Matrix.transpose_apply]

                                                                             
theorem inner_map_eq_inner_adjoint (A : PayoffOperator ι κ)
    (x : EVec ι) (y : EVec κ) :
    inner ℝ (A x) y = inner ℝ x (payoffAdjoint A y) := by
  exact (ContinuousLinearMap.adjoint_inner_right A x y).symm

                                                                           
theorem norm_map_le_opNorm (A : PayoffOperator ι κ) (x : EVec ι) :
    ‖A x‖ ≤ ‖A‖ * ‖x‖ :=
  A.le_opNorm x

                                                                                      
theorem norm_map_le_of_opNorm_le (A : PayoffOperator ι κ) {L : ℝ}
    (hA : ‖A‖ ≤ L) (x : EVec ι) :
    ‖A x‖ ≤ L * ‖x‖ := by
  exact (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg x))

                                                                        
theorem norm_payoffAdjoint (A : PayoffOperator ι κ) :
    ‖payoffAdjoint A‖ = ‖A‖ := by
  exact ContinuousLinearMap.adjoint.norm_map A

                                                                                   
theorem norm_adjoint_map_le_of_opNorm_le (A : PayoffOperator ι κ) {L : ℝ}
    (hA : ‖A‖ ≤ L) (y : EVec κ) :
    ‖payoffAdjoint A y‖ ≤ L * ‖y‖ := by
  calc
    ‖payoffAdjoint A y‖ ≤ ‖payoffAdjoint A‖ * ‖y‖ :=
      (payoffAdjoint A).le_opNorm y
    _ = ‖A‖ * ‖y‖ := by rw [norm_payoffAdjoint]
    _ ≤ L * ‖y‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg y)

                                                           
theorem abs_inner_map_le (A : PayoffOperator ι κ) (x : EVec ι) (y : EVec κ) :
    |inner ℝ (A x) y| ≤ ‖A‖ * ‖x‖ * ‖y‖ := by
  calc
    |inner ℝ (A x) y| ≤ ‖A x‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖x‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg y)

end

end AltGDA
