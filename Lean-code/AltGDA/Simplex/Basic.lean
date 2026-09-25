import AltGDA.Prelude

   
                                                     

                                                                              
                                                                           
                                                        
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι α : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

                                                              
def simplex (ι : Type*) [Fintype ι] : Set (EVec ι) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

@[simp]
theorem mem_simplex_iff {x : EVec ι} :
    x ∈ simplex ι ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
  Iff.rfl

theorem nonneg_of_mem_simplex {x : EVec ι} (hx : x ∈ simplex ι) (i : ι) :
    0 ≤ x i :=
  hx.1 i

theorem sum_eq_one_of_mem_simplex {x : EVec ι} (hx : x ∈ simplex ι) :
    ∑ i, x i = 1 :=
  hx.2

alias simplex_nonneg := nonneg_of_mem_simplex
alias simplex_sum := sum_eq_one_of_mem_simplex

theorem coordinate_le_one_of_mem_simplex {x : EVec ι} (hx : x ∈ simplex ι) (i : ι) :
    x i ≤ 1 := by
  rw [← sum_eq_one_of_mem_simplex hx]
  exact Finset.single_le_sum (fun j _ ↦ nonneg_of_mem_simplex hx j) (Finset.mem_univ i)

theorem exists_pos_of_mem_simplex {x : EVec ι} (hx : x ∈ simplex ι) :
    ∃ i, 0 < x i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hz : ∀ i, x i = 0 := fun i ↦
    le_antisymm (h i) (nonneg_of_mem_simplex hx i)
  have : (∑ i, x i) = 0 := by simp [hz]
  linarith [sum_eq_one_of_mem_simplex hx]

                                                        
def simplexVertex (i : ι) : EVec ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (Pi.single i 1)

@[simp]
theorem simplexVertex_apply (i j : ι) :
    simplexVertex i j = if j = i then 1 else 0 := by
  classical
  simp [simplexVertex]

theorem simplexVertex_mem (i : ι) : simplexVertex i ∈ simplex ι := by
  classical
  constructor
  · intro j
    simp only [simplexVertex_apply]
    split <;> positivity
  · simp only [simplexVertex_apply]
    simp

theorem simplex_nonempty : (simplex ι).Nonempty := by
  let i : ι := Classical.choice inferInstance
  exact ⟨simplexVertex i, simplexVertex_mem i⟩

theorem simplex_convex : Convex ℝ (simplex ι) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (nonneg_of_mem_simplex hx i))
      (mul_nonneg hb (nonneg_of_mem_simplex hy i))
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [sum_eq_one_of_mem_simplex hx, sum_eq_one_of_mem_simplex hy]
    simpa using hab

theorem simplex_isClosed : IsClosed (simplex ι) := by
  have hnonneg : IsClosed {x : EVec ι | ∀ i, 0 ≤ x i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i ↦
      isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)
  have hsum : IsClosed {x : EVec ι | ∑ i, x i = 1} := by
    exact isClosed_eq
      (continuous_finsetSum _ fun i _ ↦ PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)
      continuous_const
  simpa only [simplex, Set.setOf_and] using hnonneg.inter hsum

theorem simplex_norm_sq_le_one {x : EVec ι} (hx : x ∈ simplex ι) :
    ‖x‖ ^ 2 ≤ 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ i, (x i) ^ 2) ≤ ∑ i, x i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [nonneg_of_mem_simplex hx i, coordinate_le_one_of_mem_simplex hx i]
    _ = 1 := sum_eq_one_of_mem_simplex hx

theorem simplex_norm_le_one {x : EVec ι} (hx : x ∈ simplex ι) :
    ‖x‖ ≤ 1 := by
  nlinarith [simplex_norm_sq_le_one hx, norm_nonneg x]

theorem simplex_sub_norm_sq_le_two {x y : EVec ι}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex ι) :
    ‖x - y‖ ^ 2 ≤ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ i, ((x - y) i) ^ 2) ≤ ∑ i, ((x i) ^ 2 + (y i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      change (x i - y i) ^ 2 ≤ (x i) ^ 2 + (y i) ^ 2
      nlinarith [nonneg_of_mem_simplex hx i, nonneg_of_mem_simplex hy i]
    _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← EuclideanSpace.real_norm_sq_eq,
        ← EuclideanSpace.real_norm_sq_eq]
    _ ≤ 2 := by
      nlinarith [simplex_norm_sq_le_one hx, simplex_norm_sq_le_one hy]

theorem simplex_bounded : Bornology.IsBounded (simplex ι) := by
  rw [Metric.isBounded_iff]
  refine ⟨2, ?_⟩
  intro x hx y hy
  have hsq := simplex_sub_norm_sq_le_two hx hy
  have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
  rw [dist_eq_norm] at hdist_nonneg ⊢
  nlinarith [sq_nonneg (‖x - y‖ - 2)]

theorem simplex_isCompact : IsCompact (simplex ι) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨simplex_isClosed, simplex_bounded⟩

                                                                                
theorem simplex_uniformAverage_mem [Fintype α] [Nonempty α]
    (x : α → EVec ι) (hx : ∀ a, x a ∈ simplex ι) :
    ((Fintype.card α : ℝ)⁻¹ • ∑ a, x a) ∈ simplex ι := by
  classical
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  constructor
  · intro i
    simp only [PiLp.smul_apply, smul_eq_mul]
    have hsum_apply : (∑ a, x a) i = ∑ a, x a i := by
      simpa [PiLp.projₗ] using
        map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : ι ↦ ℝ) i) x Finset.univ
    rw [hsum_apply]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hcard))
      (Finset.sum_nonneg fun a _ ↦ nonneg_of_mem_simplex (hx a) i)
  · simp only [PiLp.smul_apply, smul_eq_mul]
    have hsum_apply : ∀ i, (∑ a, x a) i = ∑ a, x a i := fun i ↦ by
      simpa [PiLp.projₗ] using
        map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : ι ↦ ℝ) i) x Finset.univ
    simp_rw [hsum_apply]
    rw [← Finset.mul_sum]
    rw [show (∑ i, ∑ a, x a i) = ∑ a, ∑ i, x a i by exact Finset.sum_comm]
    simp_rw [sum_eq_one_of_mem_simplex (hx _)]
    simp [ne_of_gt hcard]

end

end AltGDA
