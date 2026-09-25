import AltGDA.Prelude

   
                                         

                                                                          
                                                                              
                               
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]

                                                   
def supportIndicator (S : Finset ι) : EVec ι :=
  ∑ j ∈ S, EuclideanSpace.single j 1

@[simp]
theorem supportIndicator_apply (S : Finset ι) (i : ι) :
    supportIndicator S i = if i ∈ S then 1 else 0 := by
  classical
  simp [supportIndicator]

theorem inner_supportIndicator (S : Finset ι) (g : EVec ι) :
    inner ℝ (supportIndicator S) g = ∑ j ∈ S, g j := by
  classical
  rw [PiLp.inner_apply]
  simp [supportIndicator_apply]

theorem supportIndicator_norm_sq (S : Finset ι) :
    ‖supportIndicator S‖ ^ 2 = S.card := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [supportIndicator_apply]

                                                         
def meanOn (S : Finset ι) (g : EVec ι) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ j ∈ S, g j

                                                             
def contrastOn (S : Finset ι) (g : EVec ι) (i : ι) : ℝ :=
  meanOn S g - g i

                                                                        
def contrastCoeff (S : Finset ι) (i : ι) : EVec ι :=
  (S.card : ℝ)⁻¹ • supportIndicator S - EuclideanSpace.single i 1

theorem inner_contrastCoeff (S : Finset ι) (g : EVec ι) (i : ι) :
    inner ℝ (contrastCoeff S i) g = contrastOn S g i := by
  classical
  simp [contrastCoeff, contrastOn, meanOn, inner_sub_left, real_inner_smul_left,
    inner_supportIndicator, EuclideanSpace.inner_single_left, Finset.mul_sum]

theorem contrastCoeff_norm_sq_of_not_mem (S : Finset ι) (i : ι)
    (hi : i ∉ S) (hS : S.Nonempty) :
    ‖contrastCoeff S i‖ ^ 2 = 1 + 1 / (S.card : ℝ) := by
  classical
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  rw [contrastCoeff, norm_sub_sq_real, norm_smul, mul_pow,
    supportIndicator_norm_sq]
  simp [PiLp.inner_apply, supportIndicator_apply, hi]
  field_simp
  ring

theorem contrastCoeff_norm_sq_of_mem (S : Finset ι) (i : ι)
    (hi : i ∈ S) (hS : S.Nonempty) :
    ‖contrastCoeff S i‖ ^ 2 = 1 - 1 / (S.card : ℝ) := by
  classical
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  rw [contrastCoeff, norm_sub_sq_real, norm_smul, mul_pow,
    supportIndicator_norm_sq]
  simp [PiLp.inner_apply, supportIndicator_apply, hi]
  field_simp
  ring

                                               
theorem abs_contrastOn_le (S : Finset ι) (g : EVec ι) (i : ι)
    (hi : i ∉ S) (hS : S.Nonempty) :
    |contrastOn S g i| ≤ Real.sqrt (1 + 1 / (S.card : ℝ)) * ‖g‖ := by
  rw [← inner_contrastCoeff]
  calc
    |inner ℝ (contrastCoeff S i) g| ≤ ‖contrastCoeff S i‖ * ‖g‖ :=
      abs_real_inner_le_norm _ _
    _ = Real.sqrt (1 + 1 / (S.card : ℝ)) * ‖g‖ := by
      congr 1
      apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      have hcard : (0 : ℝ) < S.card := by
        exact_mod_cast hS.card_pos
      have hnonneg : 0 ≤ 1 + 1 / (S.card : ℝ) := by positivity
      rw [contrastCoeff_norm_sq_of_not_mem S i hi hS, Real.sq_sqrt hnonneg]

                                                     
theorem abs_contrastOn_le_of_mem (S : Finset ι) (g : EVec ι) (i : ι)
    (hi : i ∈ S) (hS : S.Nonempty) :
    |contrastOn S g i| ≤ Real.sqrt (1 - 1 / (S.card : ℝ)) * ‖g‖ := by
  rw [← inner_contrastCoeff]
  calc
    |inner ℝ (contrastCoeff S i) g| ≤ ‖contrastCoeff S i‖ * ‖g‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (1 - 1 / (S.card : ℝ)) * ‖g‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      have hcard : (1 : ℝ) ≤ S.card := by
        exact_mod_cast hS.card_pos
      have hcard_pos : (0 : ℝ) < S.card := by positivity
      have hinv_le : (1 : ℝ) / S.card ≤ 1 := by
        exact (div_le_one hcard_pos).2 hcard
      have hnonneg : 0 ≤ 1 - 1 / (S.card : ℝ) := by linarith
      rw [contrastCoeff_norm_sq_of_mem S i hi hS, Real.sq_sqrt hnonneg]

end


end AltGDA
