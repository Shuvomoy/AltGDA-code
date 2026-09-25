import AltGDA.Analysis.ResidualBudget

   
                                

                                                                             
                                                      
  

open scoped BigOperators

namespace AltGDA

noncomputable section

theorem sum_range_shifted_pair (g : ℕ → ℝ) (T : ℕ) :
    (∑ k ∈ Finset.range T, (g (k + 1) + g (k + 2))) +
        g 1 + g (T + 1) =
      2 * ∑ k ∈ Finset.range (T + 1), g (k + 1) := by
  induction T with
  | zero =>
      simp
      ring
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num [Nat.add_assoc] at ih ⊢
      linarith

theorem sum_range_shifted_forwardDiff (a : ℕ → ℝ) (T : ℕ) :
    ∑ k ∈ Finset.range T, (a (k + 1) - a (k + 2)) =
      a 1 - a (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem sum_range_succ_eq_head_add_shift (a : ℕ → ℝ) (T : ℕ) :
    ∑ k ∈ Finset.range (T + 1), a k =
      a 0 + ∑ k ∈ Finset.range T, a (k + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
      calc
        ∑ k ∈ Finset.range (T + 1 + 1), a k =
            (∑ k ∈ Finset.range (T + 1), a k) + a (T + 1) := by
              rw [Finset.sum_range_succ]
        _ = (a 0 + ∑ k ∈ Finset.range T, a (k + 1)) + a (T + 1) := by
              rw [ih]
        _ = a 0 + ∑ k ∈ Finset.range (T + 1), a (k + 1) := by
              rw [Finset.sum_range_succ]
              ring

   
                                                                     
                                                                         
  
theorem shifted_telescope
    (g Φ r : ℕ → ℝ) (η : ℝ) (T : ℕ)
    (hstep : ∀ t, 1 ≤ t →
      η * (g t + g (t + 1)) ≤ Φ t - Φ (t + 1) + r t)
    (hr : ∀ t, 0 ≤ r t) :
    2 * η * (∑ k ∈ Finset.range (T + 1), g (k + 1)) ≤
      Φ 1 - Φ (T + 1) +
        (∑ k ∈ Finset.range (T + 1), r k) +
        η * (g 1 + g (T + 1)) := by
  have hsum :
      ∑ k ∈ Finset.range T, η * (g (k + 1) + g (k + 2)) ≤
        ∑ k ∈ Finset.range T,
          (Φ (k + 1) - Φ (k + 2) + r (k + 1)) := by
    apply Finset.sum_le_sum
    intro k _
    exact hstep (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  have hpair :
      ∑ k ∈ Finset.range T, η * (g (k + 1) + g (k + 2)) =
        η * (2 * (∑ k ∈ Finset.range (T + 1), g (k + 1)) -
          g 1 - g (T + 1)) := by
    rw [← Finset.mul_sum]
    have hp := sum_range_shifted_pair g T
    have hs :
        ∑ k ∈ Finset.range T, (g (k + 1) + g (k + 2)) =
          2 * (∑ k ∈ Finset.range (T + 1), g (k + 1)) -
            g 1 - g (T + 1) := by
      linarith
    rw [hs]
  have hright :
      ∑ k ∈ Finset.range T,
          (Φ (k + 1) - Φ (k + 2) + r (k + 1)) =
        Φ 1 - Φ (T + 1) +
          ∑ k ∈ Finset.range T, r (k + 1) := by
    rw [Finset.sum_add_distrib, sum_range_shifted_forwardDiff]
  have hrinternal :
      ∑ k ∈ Finset.range T, r (k + 1) ≤
        ∑ k ∈ Finset.range (T + 1), r k := by
    rw [sum_range_succ_eq_head_add_shift]
    linarith [hr 0]
  rw [hpair, hright] at hsum
  nlinarith

end

end AltGDA
