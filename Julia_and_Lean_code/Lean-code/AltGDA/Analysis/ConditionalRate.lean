import AltGDA.Analysis.Energy
import AltGDA.Analysis.RateFromBudget

   
                                                     

                                                                             
                                                                            
                                                              
  

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable {A : PayoffOperator ι κ}

                                                                         
theorem altGDA_rate_of_reflection_storage
    (w : GTWitness A) {L η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hstep : η ≤ w.separationDelta L / (2 * Real.sqrt 2 * L))
    (s0 : GameState ι κ) (T : ℕ) (hT : 0 < T)
    (B : ℕ → ℝ)
    (hBnonneg : ∀ t, 0 ≤ B t)
    (hB0 : B 0 ≤ 4 * Real.sqrt 2 * movementScale η L)
    (habsorb : ∀ t,
      residual A η s0 t ≤ B t - B (t + 1) +
        (1 / 2 : ℝ) * dissipation w η s0 t) :
    dualityGap A (avgX A η s0 T) (avgY A η s0 T) ≤
      15 / (2 * η * T) := by
  have hq := movementScale_le_inv_two_sqrt_two w hL hη.le hstep
  by_cases hTone : T = 1
  · subst T
    simpa using dualityGap_first_iterate_le A hL hA hη hq s0
  · have hTtwo : 2 ≤ T := by omega
    have hqTwo : movementScale η L ≤ 2 := by
      exact hq.trans (by
        have hhalf := inv_two_sqrt_two_lt_half
        linarith)
    have hbudget :
        ∑ t ∈ Finset.range T, residual A η s0 t ≤
          4 + (2 + 8 * Real.sqrt 2) * movementScale η L := by
      apply altGDA_residual_budget
        (energy w η s0) (dissipation w η s0) (residual A η s0) B T
          (movementScale η L)
      · exact energy_balance w hη s0
      · exact habsorb
      · exact hB0
      · exact hBnonneg T
      · exact energy_initial_le w hη.le hA s0
      · exact energy_nonneg_of_movementScale_le_two w hη.le hA hqTwo s0 T
    apply dualityGap_avg_le_of_residual_budget
      A hL hA hη s0 T hTtwo (residual A η s0)
    · exact residual_nonneg A hη s0
    · exact fun x hx y hy t ht ↦ combined_shifted_projection A η s0 hx hy t ht
    · simpa [movementScale] using hbudget
    · simpa [movementScale] using hq

end

end AltGDA
