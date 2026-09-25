import AltGDA.Analysis.PointwiseAbsorption

   
                                                                 

                                                                         
                                                                             
                                                                
  

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

   
                                                                           
                                                                           
                                                            
  
theorem ergodicGap_le_of_gtWitness
    (A : PayoffOperator ι κ) (w : GTWitness A) {L η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hstep : η ≤ w.separationDelta L / (2 * Real.sqrt 2 * L))
    (s0 : GameState ι κ) (T : ℕ) (hT : 0 < T) :
    dualityGap A (avgX A η s0 T) (avgY A η s0 T) ≤
      15 / (2 * η * T) :=
  altGDA_headline_rate w hL hA hη hstep s0 T hT

end

end AltGDA
