import AltGDA.Simplex.Basic

   
                                                   

                                                                              
                                                                             
                                                                           
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem exists_simplex_projection (z : EVec ι) :
    ∃ p ∈ simplex ι, ‖z - p‖ = ⨅ u : simplex ι, ‖z - u‖ :=
  exists_norm_eq_iInf_of_complete_convex simplex_nonempty
    simplex_isCompact.isComplete simplex_convex z

                                                                       
def simplexProj (z : EVec ι) : EVec ι :=
  Classical.choose (exists_simplex_projection z)

theorem simplexProj_mem (z : EVec ι) : simplexProj z ∈ simplex ι :=
  (Classical.choose_spec (exists_simplex_projection z)).1

theorem simplexProj_norm_eq_iInf (z : EVec ι) :
    ‖z - simplexProj z‖ = ⨅ u : simplex ι, ‖z - u‖ :=
  (Classical.choose_spec (exists_simplex_projection z)).2

                                                                    
theorem simplexProj_minimal (z : EVec ι) {u : EVec ι} (hu : u ∈ simplex ι) :
    ‖simplexProj z - z‖ ≤ ‖u - z‖ := by
  have h : ‖z - simplexProj z‖ ≤ ‖z - u‖ := by
    rw [simplexProj_norm_eq_iInf]
    have hb : BddBelow (Set.range fun v : simplex ι ↦ ‖z - (v : EVec ι)‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨v, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hb ⟨u, hu⟩
  simpa only [norm_sub_rev] using h

                                                                             
theorem simplexProj_variational_inequality (z : EVec ι) {u : EVec ι}
    (hu : u ∈ simplex ι) :
    ⟪z - simplexProj z, u - simplexProj z⟫ ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero simplex_convex (simplexProj_mem z)).mp
    (simplexProj_norm_eq_iInf z) u hu

                                                   
@[simp]
theorem simplexProj_fixed {x : EVec ι} (hx : x ∈ simplex ι) :
    simplexProj x = x := by
  have hmin := simplexProj_minimal x hx
  rw [sub_self, norm_zero] at hmin
  have hz : ‖simplexProj x - x‖ = 0 := le_antisymm hmin (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

                                                                   
theorem simplexProj_firmly_nonexpansive (z w : EVec ι) :
    ‖simplexProj z - simplexProj w‖ ^ 2 ≤
      ⟪z - w, simplexProj z - simplexProj w⟫ := by
  have hz := simplexProj_variational_inequality z (simplexProj_mem w)
  have hw := simplexProj_variational_inequality w (simplexProj_mem z)
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm] at hz hw ⊢
  linarith

                                                             
theorem simplexProj_nonexpansive (z w : EVec ι) :
    ‖simplexProj z - simplexProj w‖ ≤ ‖z - w‖ := by
  have hfirm := simplexProj_firmly_nonexpansive z w
  have hcs := real_inner_le_norm (z - w) (simplexProj z - simplexProj w)
  by_cases hz : ‖simplexProj z - simplexProj w‖ = 0
  · simp [hz]
  · have hpos : 0 < ‖simplexProj z - simplexProj w‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

                                                                           
                        
theorem simplexProj_movement_le {x h : EVec ι} (hx : x ∈ simplex ι) :
    ‖simplexProj (x + h) - x‖ ≤ ‖h‖ := by
  calc
    ‖simplexProj (x + h) - x‖ = ‖simplexProj (x + h) - simplexProj x‖ := by
      rw [simplexProj_fixed hx]
    _ ≤ ‖(x + h) - x‖ := simplexProj_nonexpansive _ _
    _ = ‖h‖ := by rw [add_sub_cancel_left]

                                                                       
theorem simplexProj_sqdist_le (z : EVec ι) {u : EVec ι} (hu : u ∈ simplex ι) :
    ‖simplexProj z - u‖ ^ 2 ≤ ‖z - u‖ ^ 2 - ‖z - simplexProj z‖ ^ 2 := by
  have hvi := simplexProj_variational_inequality z hu
  have hdecomp : z - u = (z - simplexProj z) - (u - simplexProj z) := by abel
  have hexpand :
      ‖z - u‖ ^ 2 = ‖z - simplexProj z‖ ^ 2 -
        2 * ⟪z - simplexProj z, u - simplexProj z⟫ +
        ‖u - simplexProj z‖ ^ 2 := by
    rw [hdecomp, @norm_sub_sq ℝ]
    rfl
  rw [hexpand, norm_sub_rev (simplexProj z) u]
  nlinarith

                                                                                    
theorem simplexProj_inner_update_nonneg (z : EVec ι) {u : EVec ι}
    (hu : u ∈ simplex ι) :
    0 ≤ ⟪simplexProj z - z, u - simplexProj z⟫ := by
  have hvi := simplexProj_variational_inequality z hu
  rw [show simplexProj z - z = -(z - simplexProj z) by abel, inner_neg_left]
  linarith

end

end AltGDA
