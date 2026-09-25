import AltGDA.Simplex.Projection

   
                                            

                                                                          
                                                                          
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem inner_simplexVertex (v : EVec ι) (i : ι) :
    ⟪v, simplexVertex i⟫ = v i := by
  classical
  rw [PiLp.inner_apply]
  simp [simplexVertex_apply]

                                                                 
def simplexProjectionThreshold (z : EVec ι) : ℝ :=
  ⟪z - simplexProj z, simplexProj z⟫

                                                                                     
def simplexProjectionMultiplier (z : EVec ι) : EVec ι :=
  simplexProjectionThreshold z • ones ι - (z - simplexProj z)

@[simp]
theorem simplexProjectionMultiplier_apply (z : EVec ι) (i : ι) :
    simplexProjectionMultiplier z i =
      simplexProjectionThreshold z - (z i - simplexProj z i) := by
  simp [simplexProjectionMultiplier]

theorem simplexProjectionMultiplier_nonneg (z : EVec ι) (i : ι) :
    0 ≤ simplexProjectionMultiplier z i := by
  have hvi := simplexProj_variational_inequality z (simplexVertex_mem i)
  rw [inner_sub_right, inner_simplexVertex] at hvi
  change (z - simplexProj z) i - simplexProjectionThreshold z ≤ 0 at hvi
  rw [simplexProjectionMultiplier_apply]
  change 0 ≤ simplexProjectionThreshold z - (z - simplexProj z) i
  linarith

theorem simplexProjection_stationarity (z : EVec ι) :
    simplexProj z = z - simplexProjectionThreshold z • ones ι +
      simplexProjectionMultiplier z := by
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, ones_apply,
    smul_eq_mul, simplexProjectionMultiplier_apply]
  ring

theorem simplexProjection_displacement (z : EVec ι) :
    z - simplexProj z = simplexProjectionThreshold z • ones ι -
      simplexProjectionMultiplier z := by
  rw [simplexProjection_stationarity z]
  abel

theorem simplexProjection_complementarity (z : EVec ι) (i : ι) :
    simplexProjectionMultiplier z i * simplexProj z i = 0 := by
  have hterm : ∀ j, 0 ≤ simplexProjectionMultiplier z j * simplexProj z j := fun j ↦
    mul_nonneg (simplexProjectionMultiplier_nonneg z j)
      (nonneg_of_mem_simplex (simplexProj_mem z) j)
  have hinter :
      (∑ j, (z j - simplexProj z j) * simplexProj z j) =
        simplexProjectionThreshold z := by
    rw [simplexProjectionThreshold, PiLp.inner_apply]
    simp only [PiLp.sub_apply, Real.inner_apply]
  have hsum :
      (∑ j, simplexProjectionMultiplier z j * simplexProj z j) = 0 := by
    simp_rw [simplexProjectionMultiplier_apply, sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_eq_one_of_mem_simplex (simplexProj_mem z), mul_one]
    rw [show (∑ j, (z j * simplexProj z j - simplexProj z j * simplexProj z j)) =
        simplexProjectionThreshold z by simpa only [sub_mul] using hinter]
    ring
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hterm j).mp hsum i (Finset.mem_univ i)

                                                         
structure SimplexProjectionKKT (z p : EVec ι) where
  threshold : ℝ
  multiplier : EVec ι
  stationarity : p = z - threshold • ones ι + multiplier
  multiplier_nonneg : ∀ i, 0 ≤ multiplier i
  complementarity : ∀ i, multiplier i * p i = 0

                                                                                  
def simplexProj_kkt (z : EVec ι) :
    SimplexProjectionKKT z (simplexProj z) where
  threshold := simplexProjectionThreshold z
  multiplier := simplexProjectionMultiplier z
  stationarity := simplexProjection_stationarity z
  multiplier_nonneg := simplexProjectionMultiplier_nonneg z
  complementarity := simplexProjection_complementarity z

                                                                      
structure SimplexProjectedStepKKT (p g : EVec ι) (η : ℝ) where
  threshold : ℝ
  multiplier : EVec ι
  multiplier_nonneg : ∀ i, 0 ≤ multiplier i
  displacement : simplexProj (p + η • g) - p =
    η • (g - threshold • ones ι + multiplier)
  complementarity : ∀ i, multiplier i * simplexProj (p + η • g) i = 0

                                                                               
                            
def simplexProj_step_kkt (p g : EVec ι) {η : ℝ} (hη : 0 < η) :
    SimplexProjectedStepKKT p g η where
  threshold := simplexProjectionThreshold (p + η • g) / η
  multiplier := η⁻¹ • simplexProjectionMultiplier (p + η • g)
  multiplier_nonneg := by
    intro i
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hη))
      (simplexProjectionMultiplier_nonneg _ i)
  displacement := by
    rw [simplexProjection_stationarity (p + η • g)]
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, ones_apply, smul_eq_mul]
    field_simp [ne_of_gt hη]
    ring
  complementarity := by
    intro i
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [mul_assoc, simplexProjection_complementarity, mul_zero]

end

end AltGDA
