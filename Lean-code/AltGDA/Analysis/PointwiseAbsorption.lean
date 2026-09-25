import AltGDA.Analysis.ReflectionY
import AltGDA.Analysis.ConditionalRate

   
                                                

                                                                        
                                                                          
                                                                          
                                                                             
                                                 
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable {A : PayoffOperator ι κ}

                                                                   
def boundaryStorage (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  storageX w η s0 t + storageY w η s0 t

                                                                           
                                          
def reflectionStorage (w : GTWitness A) (L η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  boundaryStorage w η s0 t + 2 * Real.sqrt 2 * movementScale η L

                                                              
theorem abs_boundaryStorage_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 ≤ η)
    (s0 : GameState ι κ) (t : ℕ) :
    |boundaryStorage w η s0 t| ≤
      2 * Real.sqrt 2 * movementScale η L := by
  calc
    |boundaryStorage w η s0 t| ≤
        |storageX w η s0 t| + |storageY w η s0 t| := by
      simpa [boundaryStorage] using
        (abs_add_le (storageX w η s0 t) (storageY w η s0 t))
    _ ≤ Real.sqrt 2 * (η * L) + Real.sqrt 2 * (η * L) :=
      add_le_add (abs_storageX_le w hL hA hη s0 t)
        (abs_storageY_le w hL hA hη s0 t)
    _ = 2 * Real.sqrt 2 * movementScale η L := by
      simp [movementScale]
      ring

                                                        
theorem reflectionStorage_nonneg (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 ≤ η)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ reflectionStorage w L η s0 t := by
  have h := neg_le_of_abs_le (abs_boundaryStorage_le w hL hA hη s0 t)
  unfold reflectionStorage
  linarith

                                                                    
theorem reflectionStorage_zero_le_four_sqrtTwo (w : GTWitness A)
    {L η : ℝ} (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 ≤ η)
    (s0 : GameState ι κ) :
    reflectionStorage w L η s0 0 ≤
      4 * Real.sqrt 2 * movementScale η L := by
  have h := le_of_abs_le (abs_boundaryStorage_le w hL hA hη s0 0)
  unfold reflectionStorage
  linarith

                                                                      
                                                                      
theorem pointwiseResidualAbsorption (w : GTWitness A) {L δ η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hb : w.SeparationBounds L δ)
    (hstep : η * L ≤ δ / (2 * Real.sqrt 2))
    (s0 : GameState ι κ) (t : ℕ) :
    residual A η s0 t ≤
      reflectionStorage w L η s0 t -
        reflectionStorage w L η s0 (t + 1) +
        (1 / 2 : ℝ) * dissipation w η s0 t := by
  have hx := xBlockBound w hL hA hη hb hstep s0 t
  have hy := yBlockBound w hL hA hη hb hstep s0 t
  have hblocks :
      η * (inner ℝ (muKKT A η s0 t) (xIter A η s0 t) +
        inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t)) ≤
        boundaryStorage w η s0 t - boundaryStorage w η s0 (t + 1) +
        (η / 2) * slackMass w η s0 t +
        (η / 2) * equilibriumMultiplier w η s0 t := by
    unfold boundaryStorage slackMass equilibriumMultiplier
    nlinarith [add_le_add hx hy]
  have hpnext : 0 ≤ η * slackMass w η s0 (t + 1) :=
    mul_nonneg hη.le (slackMass_nonneg w η s0 (t + 1))
  have heq : 0 ≤ η * equilibriumMultiplier w η s0 t :=
    mul_nonneg hη.le (equilibriumMultiplier_nonneg w hη s0 t)
  have hdiss :
      (η / 2) * slackMass w η s0 t +
          (η / 2) * equilibriumMultiplier w η s0 t ≤
        (1 / 2 : ℝ) * dissipation w η s0 t := by
    unfold dissipation
    nlinarith
  rw [residual_eq_eta_mul_pairings A hη s0 t]
  unfold reflectionStorage
  nlinarith

                                                                             
theorem canonicalPointwiseResidualAbsorption (w : GTWitness A) {L η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hstep : η ≤ w.separationDelta L / (2 * Real.sqrt 2 * L))
    (s0 : GameState ι κ) (t : ℕ) :
    residual A η s0 t ≤
      reflectionStorage w L η s0 t -
        reflectionStorage w L η s0 (t + 1) +
        (1 / 2 : ℝ) * dissipation w η s0 t := by
  have hstepq : η * L ≤ w.separationDelta L / (2 * Real.sqrt 2) := by
    calc
      η * L ≤ (w.separationDelta L / (2 * Real.sqrt 2 * L)) * L :=
        mul_le_mul_of_nonneg_right hstep hL.le
      _ = w.separationDelta L / (2 * Real.sqrt 2) := by
        field_simp [hL.ne']
  exact pointwiseResidualAbsorption w hL hA hη
    (w.canonicalSeparationBounds hL) hstepq s0 t

                                                                            
theorem altGDA_headline_rate (w : GTWitness A) {L η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hstep : η ≤ w.separationDelta L / (2 * Real.sqrt 2 * L))
    (s0 : GameState ι κ) (T : ℕ) (hT : 0 < T) :
    dualityGap A (avgX A η s0 T) (avgY A η s0 T) ≤
      15 / (2 * η * T) := by
  apply altGDA_rate_of_reflection_storage w hL hA hη hstep s0 T hT
    (reflectionStorage w L η s0)
  · exact fun t ↦ reflectionStorage_nonneg w hL.le hA hη.le s0 t
  · exact reflectionStorage_zero_le_four_sqrtTwo w hL.le hA hη.le s0
  · exact fun t ↦
      canonicalPointwiseResidualAbsorption w hL hA hη hstep s0 t

end

end AltGDA
