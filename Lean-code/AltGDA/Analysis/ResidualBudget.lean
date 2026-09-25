import AltGDA.Analysis.Constants

   
                                      

                                                                    
                                                                        
                                                                       
                                                       
  

open scoped BigOperators

namespace AltGDA

noncomputable section

                                                           
theorem sum_range_forwardDiff (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (a (t + 1) - a t) = a T - a 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring

   
                                                                  

                                                                           
                                                      
                           
  
theorem residual_budget_of_energy_and_storage
    (V D r B : ℕ → ℝ) (T : ℕ) (C q : ℝ)
    (henergy : ∀ t, V (t + 1) - V t + D t = r t)
    (habsorb : ∀ t, r t ≤ B t - B (t + 1) + (1 / 2 : ℝ) * D t)
    (hB0 : B 0 ≤ C) (hBT : 0 ≤ B T)
    (hV0 : V 0 ≤ 4 + 2 * q) (hVT : 0 ≤ V T) :
    ∑ t ∈ Finset.range T, r t ≤ 2 * C + 4 + 2 * q := by
  have hsumAbsorb :
      ∑ t ∈ Finset.range T, r t ≤
        ∑ t ∈ Finset.range T,
          (B t - B (t + 1) + (1 / 2 : ℝ) * D t) := by
    exact Finset.sum_le_sum fun t _ ↦ habsorb t
  have hstorage :
      ∑ t ∈ Finset.range T, (B t - B (t + 1)) = B 0 - B T := by
    calc
      ∑ t ∈ Finset.range T, (B t - B (t + 1)) =
          -(∑ t ∈ Finset.range T, (B (t + 1) - B t)) := by
            simp only [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ = -(B T - B 0) := by rw [sum_range_forwardDiff]
      _ = B 0 - B T := by ring
  have hres_le :
      ∑ t ∈ Finset.range T, r t ≤
        C + (1 / 2 : ℝ) * (∑ t ∈ Finset.range T, D t) := by
    calc
      ∑ t ∈ Finset.range T, r t ≤
          ∑ t ∈ Finset.range T,
            (B t - B (t + 1) + (1 / 2 : ℝ) * D t) := hsumAbsorb
      _ = (B 0 - B T) +
          (1 / 2 : ℝ) * (∑ t ∈ Finset.range T, D t) := by
            rw [Finset.sum_add_distrib, hstorage, ← Finset.mul_sum]
      _ ≤ C + (1 / 2 : ℝ) * (∑ t ∈ Finset.range T, D t) := by
            linarith
  have henergySum :
      V T - V 0 + (∑ t ∈ Finset.range T, D t) =
        ∑ t ∈ Finset.range T, r t := by
    calc
      V T - V 0 + (∑ t ∈ Finset.range T, D t) =
          (∑ t ∈ Finset.range T, (V (t + 1) - V t)) +
            (∑ t ∈ Finset.range T, D t) := by
              rw [sum_range_forwardDiff]
      _ = ∑ t ∈ Finset.range T,
          (V (t + 1) - V t + D t) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ t ∈ Finset.range T, r t := by
            apply Finset.sum_congr rfl
            intro t _
            exact henergy t
  linarith

                                                                        
theorem altGDA_residual_budget
    (V D r B : ℕ → ℝ) (T : ℕ) (q : ℝ)
    (henergy : ∀ t, V (t + 1) - V t + D t = r t)
    (habsorb : ∀ t, r t ≤ B t - B (t + 1) + (1 / 2 : ℝ) * D t)
    (hB0 : B 0 ≤ 4 * Real.sqrt 2 * q) (hBT : 0 ≤ B T)
    (hV0 : V 0 ≤ 4 + 2 * q) (hVT : 0 ≤ V T) :
    ∑ t ∈ Finset.range T, r t ≤ 4 + (2 + 8 * Real.sqrt 2) * q := by
  have h := residual_budget_of_energy_and_storage V D r B T
    (4 * Real.sqrt 2 * q) q henergy habsorb hB0 hBT hV0 hVT
  nlinarith

end

end AltGDA
