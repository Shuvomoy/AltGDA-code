import AltGDA.MainTheorem
import AltGDA.Game.GoldmanTuckerExistence

   
                                              

                                                                         
                                                                            
                                                                    
  

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

   
                                                                             
                                                                            
                                                                          
                                                             
  
theorem manuscript_main_theorem (M : Matrix κ ι ℝ) :
    ∃ w : GTWitness (matrixOperator M),
      ∀ (L η : ℝ), 0 < L → ‖matrixOperator M‖ ≤ L → 0 < η →
        η ≤ w.separationDelta L / (2 * Real.sqrt 2 * L) →
          ∀ (s0 : GameState ι κ) (T : ℕ), 0 < T →
            dualityGap (matrixOperator M)
                (avgX (matrixOperator M) η s0 T)
                (avgY (matrixOperator M) η s0 T) ≤
              15 / (2 * η * T) := by
  obtain ⟨w⟩ := exists_gtWitness (matrixOperator M)
  refine ⟨w, ?_⟩
  intro L η hL hM hη hstep s0 T hT
  exact ergodicGap_le_of_gtWitness
    (matrixOperator M) w hL hM hη hstep s0 T hT

end

end AltGDA
