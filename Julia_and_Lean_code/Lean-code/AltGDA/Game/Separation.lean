import AltGDA.Game.Witness

   
                                                            

                                                                            
                                                                       
                                                                    
  

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable {A : PayoffOperator ι κ}

namespace GTWitness

variable (w : GTWitness A)

                                                                           
def underlineX : ℝ :=
  w.supportX.inf' w.supportX_nonempty w.xStar

                                                                           
def underlineY : ℝ :=
  w.supportY.inf' w.supportY_nonempty w.yStar

                                                                                        
def sigmaX (h : w.offSupportX.Nonempty) : ℝ :=
  w.offSupportX.inf' h w.slackX

                                                                                        
def sigmaY (h : w.offSupportY.Nonempty) : ℝ :=
  w.offSupportY.inf' h w.slackY

theorem underlineX_pos : 0 < w.underlineX := by
  rw [underlineX, Finset.lt_inf'_iff]
  intro i hi
  exact (w.mem_supportX).mp hi

theorem underlineY_pos : 0 < w.underlineY := by
  rw [underlineY, Finset.lt_inf'_iff]
  intro j hj
  exact (w.mem_supportY).mp hj

theorem underlineX_le {i : ι} (hi : i ∈ w.supportX) :
    w.underlineX ≤ w.xStar i := by
  exact Finset.inf'_le w.xStar hi

theorem underlineY_le {j : κ} (hj : j ∈ w.supportY) :
    w.underlineY ≤ w.yStar j := by
  exact Finset.inf'_le w.yStar hj

theorem sigmaX_pos (h : w.offSupportX.Nonempty) : 0 < w.sigmaX h := by
  rw [sigmaX, Finset.lt_inf'_iff]
  intro i hi
  exact w.slackX_pos_of_mem_offSupport hi

theorem sigmaY_pos (h : w.offSupportY.Nonempty) : 0 < w.sigmaY h := by
  rw [sigmaY, Finset.lt_inf'_iff]
  intro j hj
  exact w.slackY_pos_of_mem_offSupport hj

theorem sigmaX_le (h : w.offSupportX.Nonempty) {i : ι}
    (hi : i ∈ w.offSupportX) :
    w.sigmaX h ≤ w.slackX i := by
  exact Finset.inf'_le w.slackX hi

theorem sigmaY_le (h : w.offSupportY.Nonempty) {j : κ}
    (hj : j ∈ w.offSupportY) :
    w.sigmaY h ≤ w.slackY j := by
  exact Finset.inf'_le w.slackY hj

   
                                                                       
                                                                            
      
  
def xSeparation (L : ℝ) : ℝ :=
  if h : w.offSupportX.Nonempty then
    min w.underlineX (w.sigmaX h / L)
  else
    w.underlineX

                                                                             
def ySeparation (L : ℝ) : ℝ :=
  if h : w.offSupportY.Nonempty then
    min w.underlineY (w.sigmaY h / L)
  else
    w.underlineY

   
                                     
                                                                         
  
def separationDelta (L : ℝ) : ℝ :=
  min (w.xSeparation L) (w.ySeparation L)

theorem xSeparation_eq_of_offSupport_nonempty (L : ℝ)
    (h : w.offSupportX.Nonempty) :
    w.xSeparation L = min w.underlineX (w.sigmaX h / L) := by
  simp [xSeparation, h]

theorem xSeparation_eq_of_offSupport_empty (L : ℝ)
    (h : ¬ w.offSupportX.Nonempty) :
    w.xSeparation L = w.underlineX := by
  simp [xSeparation, h]

theorem ySeparation_eq_of_offSupport_nonempty (L : ℝ)
    (h : w.offSupportY.Nonempty) :
    w.ySeparation L = min w.underlineY (w.sigmaY h / L) := by
  simp [ySeparation, h]

theorem ySeparation_eq_of_offSupport_empty (L : ℝ)
    (h : ¬ w.offSupportY.Nonempty) :
    w.ySeparation L = w.underlineY := by
  simp [ySeparation, h]

theorem xSeparation_pos {L : ℝ} (hL : 0 < L) :
    0 < w.xSeparation L := by
  by_cases h : w.offSupportX.Nonempty
  · rw [w.xSeparation_eq_of_offSupport_nonempty L h]
    exact lt_min w.underlineX_pos (div_pos (w.sigmaX_pos h) hL)
  · rw [w.xSeparation_eq_of_offSupport_empty L h]
    exact w.underlineX_pos

theorem ySeparation_pos {L : ℝ} (hL : 0 < L) :
    0 < w.ySeparation L := by
  by_cases h : w.offSupportY.Nonempty
  · rw [w.ySeparation_eq_of_offSupport_nonempty L h]
    exact lt_min w.underlineY_pos (div_pos (w.sigmaY_pos h) hL)
  · rw [w.ySeparation_eq_of_offSupport_empty L h]
    exact w.underlineY_pos

theorem separationDelta_pos {L : ℝ} (hL : 0 < L) :
    0 < w.separationDelta L := by
  exact lt_min (w.xSeparation_pos hL) (w.ySeparation_pos hL)

theorem separationDelta_le_xSeparation (L : ℝ) :
    w.separationDelta L ≤ w.xSeparation L := by
  exact min_le_left _ _

theorem separationDelta_le_ySeparation (L : ℝ) :
    w.separationDelta L ≤ w.ySeparation L := by
  exact min_le_right _ _

theorem xSeparation_le_underlineX (L : ℝ) :
    w.xSeparation L ≤ w.underlineX := by
  by_cases h : w.offSupportX.Nonempty
  · rw [w.xSeparation_eq_of_offSupport_nonempty L h]
    exact min_le_left _ _
  · rw [w.xSeparation_eq_of_offSupport_empty L h]

theorem ySeparation_le_underlineY (L : ℝ) :
    w.ySeparation L ≤ w.underlineY := by
  by_cases h : w.offSupportY.Nonempty
  · rw [w.ySeparation_eq_of_offSupport_nonempty L h]
    exact min_le_left _ _
  · rw [w.ySeparation_eq_of_offSupport_empty L h]

theorem separationDelta_le_underlineX (L : ℝ) :
    w.separationDelta L ≤ w.underlineX :=
  (w.separationDelta_le_xSeparation L).trans (w.xSeparation_le_underlineX L)

theorem separationDelta_le_underlineY (L : ℝ) :
    w.separationDelta L ≤ w.underlineY :=
  (w.separationDelta_le_ySeparation L).trans (w.ySeparation_le_underlineY L)

theorem separationDelta_le_sigmaX_div (L : ℝ)
    (h : w.offSupportX.Nonempty) :
    w.separationDelta L ≤ w.sigmaX h / L := by
  calc
    w.separationDelta L ≤ w.xSeparation L :=
      w.separationDelta_le_xSeparation L
    _ = min w.underlineX (w.sigmaX h / L) :=
      w.xSeparation_eq_of_offSupport_nonempty L h
    _ ≤ w.sigmaX h / L := min_le_right _ _

theorem separationDelta_le_sigmaY_div (L : ℝ)
    (h : w.offSupportY.Nonempty) :
    w.separationDelta L ≤ w.sigmaY h / L := by
  calc
    w.separationDelta L ≤ w.ySeparation L :=
      w.separationDelta_le_ySeparation L
    _ = min w.underlineY (w.sigmaY h / L) :=
      w.ySeparation_eq_of_offSupport_nonempty L h
    _ ≤ w.sigmaY h / L := min_le_right _ _

theorem separationDelta_le_xStar (L : ℝ) {i : ι} (hi : i ∈ w.supportX) :
    w.separationDelta L ≤ w.xStar i :=
  (w.separationDelta_le_underlineX L).trans (w.underlineX_le hi)

theorem separationDelta_le_yStar (L : ℝ) {j : κ} (hj : j ∈ w.supportY) :
    w.separationDelta L ≤ w.yStar j :=
  (w.separationDelta_le_underlineY L).trans (w.underlineY_le hj)

theorem separationDelta_le_slackX_div {L : ℝ} (hL : 0 < L)
    {i : ι} (hi : i ∈ w.offSupportX) :
    w.separationDelta L ≤ w.slackX i / L := by
  have hne : w.offSupportX.Nonempty := ⟨i, hi⟩
  calc
    w.separationDelta L ≤ w.sigmaX hne / L :=
      w.separationDelta_le_sigmaX_div L hne
    _ ≤ w.slackX i / L :=
      (div_le_div_iff_of_pos_right hL).2 (w.sigmaX_le hne hi)

theorem separationDelta_le_slackY_div {L : ℝ} (hL : 0 < L)
    {j : κ} (hj : j ∈ w.offSupportY) :
    w.separationDelta L ≤ w.slackY j / L := by
  have hne : w.offSupportY.Nonempty := ⟨j, hj⟩
  calc
    w.separationDelta L ≤ w.sigmaY hne / L :=
      w.separationDelta_le_sigmaY_div L hne
    _ ≤ w.slackY j / L :=
      (div_le_div_iff_of_pos_right hL).2 (w.sigmaY_le hne hj)

theorem separationDelta_mul_le_slackX {L : ℝ} (hL : 0 < L)
    {i : ι} (hi : i ∈ w.offSupportX) :
    w.separationDelta L * L ≤ w.slackX i := by
  calc
    w.separationDelta L * L ≤ (w.slackX i / L) * L :=
      mul_le_mul_of_nonneg_right (w.separationDelta_le_slackX_div hL hi) hL.le
    _ = w.slackX i := div_mul_cancel₀ _ hL.ne'

theorem separationDelta_mul_le_slackY {L : ℝ} (hL : 0 < L)
    {j : κ} (hj : j ∈ w.offSupportY) :
    w.separationDelta L * L ≤ w.slackY j := by
  calc
    w.separationDelta L * L ≤ (w.slackY j / L) * L :=
      mul_le_mul_of_nonneg_right (w.separationDelta_le_slackY_div hL hj) hL.le
    _ = w.slackY j := div_mul_cancel₀ _ hL.ne'

theorem separationDelta_le_one (L : ℝ) : w.separationDelta L ≤ 1 := by
  obtain ⟨i, hi⟩ := w.supportX_nonempty
  exact (w.separationDelta_le_xStar L hi).trans
    (coordinate_le_one_of_mem_simplex w.x_mem i)

   
                                                                        
                                                                            
                               
  
structure SeparationBounds (L δ : ℝ) : Prop where
  positive : 0 < δ
  le_one : δ ≤ 1
  le_xStar : ∀ i ∈ w.supportX, δ ≤ w.xStar i
  le_yStar : ∀ j ∈ w.supportY, δ ≤ w.yStar j
  le_slackX_div : ∀ i ∈ w.offSupportX, δ ≤ w.slackX i / L
  le_slackY_div : ∀ j ∈ w.offSupportY, δ ≤ w.slackY j / L
  mul_L_le_slackX : ∀ i ∈ w.offSupportX, δ * L ≤ w.slackX i
  mul_L_le_slackY : ∀ j ∈ w.offSupportY, δ * L ≤ w.slackY j

                                                                               
theorem canonicalSeparationBounds {L : ℝ} (hL : 0 < L) :
    w.SeparationBounds L (w.separationDelta L) where
  positive := w.separationDelta_pos hL
  le_one := w.separationDelta_le_one L
  le_xStar := fun _ hi ↦ w.separationDelta_le_xStar L hi
  le_yStar := fun _ hj ↦ w.separationDelta_le_yStar L hj
  le_slackX_div := fun _ hi ↦ w.separationDelta_le_slackX_div hL hi
  le_slackY_div := fun _ hj ↦ w.separationDelta_le_slackY_div hL hj
  mul_L_le_slackX := fun _ hi ↦ w.separationDelta_mul_le_slackX hL hi
  mul_L_le_slackY := fun _ hj ↦ w.separationDelta_mul_le_slackY hL hj

end GTWitness

end

end AltGDA
