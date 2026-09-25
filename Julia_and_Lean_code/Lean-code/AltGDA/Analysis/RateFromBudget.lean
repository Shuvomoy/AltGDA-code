import AltGDA.Analysis.GapTelescope

   
                                                 

                                                                             
                                                                           
                                                                      
                                            
  

open scoped BigOperators

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                        
theorem dualityGap_avg_le_of_residual_budget
    (A : PayoffOperator ι κ) {L η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (T : ℕ) (hT : 2 ≤ T)
    (r : ℕ → ℝ)
    (hr : ∀ t, 0 ≤ r t)
    (hcombined : ∀ x ∈ simplex ι, ∀ y ∈ simplex κ, ∀ t,
      1 ≤ t →
      η * (comparatorGap A η s0 x y t +
        comparatorGap A η s0 x y (t + 1)) ≤
        shiftedPotential A η s0 x y t -
          shiftedPotential A η s0 x y (t + 1) + r t)
    (hbudget : ∑ t ∈ Finset.range T, r t ≤
      4 + (2 + 8 * Real.sqrt 2) * (η * L))
    (hq : η * L ≤ (1 : ℝ) / (2 * Real.sqrt 2)) :
    dualityGap A (avgX A η s0 T) (avgY A η s0 T) ≤
      15 / (2 * η * T) := by
  apply dualityGap_avg_le_of_comparator_sum A hη s0 T (by omega)
  intro x hx y hy
  let n := T - 1
  have hn : n + 1 = T := by
    dsimp [n]
    omega
  have htel := shifted_telescope
    (comparatorGap A η s0 x y)
    (shiftedPotential A η s0 x y) r η n
    (hcombined x hx y hy) hr
  rw [hn] at htel
  have hfirst := shiftedPotential_one_le A hA hη.le s0 hx hy
  have hlast := neg_shiftedPotential_le A hL hA hη s0 hx hy T (by omega)
  have hend := comparatorGap_endpoints_le A hA hη.le s0 hx hy T
  have htotal :
      2 * η * (∑ k ∈ Finset.range T,
        comparatorGap A η s0 x y (k + 1)) ≤
        8 + (8 + 8 * Real.sqrt 2) * (η * L) +
          (η * L) ^ 2 / 2 := by
    nlinarith
  have hq0 : 0 ≤ η * L := mul_nonneg hη.le hL.le
  have hnumeric := final_expression_lt_fifteen hq0 hq
  linarith

                                                                              
theorem dualityGap_first_iterate_le
    (A : PayoffOperator ι κ) {L η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hq : η * L ≤ (1 : ℝ) / (2 * Real.sqrt 2))
    (s0 : GameState ι κ) :
    dualityGap A (avgX A η s0 1) (avgY A η s0 1) ≤
      15 / (2 * η) := by
  have havgx : avgX A η s0 1 = xIter A η s0 1 := by
    simp [avgX]
  have havgy : avgY A η s0 1 = yIter A η s0 1 := by
    simp [avgY]
  rw [havgx, havgy]
  have hgap := dualityGap_le_two_opNorm A
    (xIter_mem A η s0 1) (yIter_mem A η s0 1)
  have hgapL :
      dualityGap A (xIter A η s0 1) (yIter A η s0 1) ≤ 2 * L :=
    hgap.trans (mul_le_mul_of_nonneg_left hA (by norm_num))
  have hηgap :
      η * dualityGap A (xIter A η s0 1) (yIter A η s0 1) ≤
        2 * (η * L) := by
    nlinarith
  have hsmall : 2 * (η * L) < 15 / 2 := by
    have hinvlt := inv_two_sqrt_two_lt_half
    nlinarith
  apply (le_div_iff₀ (show 0 < 2 * η by positivity)).2
  nlinarith

end

end AltGDA
