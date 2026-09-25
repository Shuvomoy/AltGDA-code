import AltGDA.Analysis.ReflectionX

   
                                          

                                                                      
                                                                       
                                                                        
                                        
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable {A : PayoffOperator ι κ}

                                                                 
def offMassY (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  ∑ j ∈ w.offSupportY, yIter A η s0 t j

                                                    
def deltaOffMassY (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  offMassY w η s0 (t + 1) - offMassY w η s0 t

                                                                    
def contrastY (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) (j : κ) : ℝ :=
  contrastOn w.supportY (A (xIter A η s0 t)) j

                                                       
def meanRhoY (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  meanOn w.supportY (rhoKKT A η s0 t)

                                                                  
def storageY (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  η * ∑ j ∈ w.offSupportY,
    contrastY w η s0 t j * yIter A η s0 t j

                                                                                   
theorem sum_supportY_add_offSupportY (w : GTWitness A) (f : κ → ℝ) :
    (∑ j ∈ w.supportY, f j) + (∑ j ∈ w.offSupportY, f j) = ∑ j, f j := by
  classical
  rw [GTWitness.offSupportY]
  rw [add_comm, Finset.sum_sdiff (Finset.subset_univ w.supportY)]

                                                                     
theorem sum_deltaY_eq_zero (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    ∑ j, deltaY A η s0 t j = 0 := by
  simp [deltaY, Finset.sum_sub_distrib,
    sum_eq_one_of_mem_simplex (yIter_mem A η s0 (t + 1)),
    sum_eq_one_of_mem_simplex (yIter_mem A η s0 t)]

                                                                          
theorem deltaOffMassY_eq_sum_deltaY (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    deltaOffMassY w η s0 t = ∑ j ∈ w.offSupportY, deltaY A η s0 t j := by
  simp [deltaOffMassY, offMassY, deltaY, Finset.sum_sub_distrib]

                                                                       
theorem sum_supportY_deltaY (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    ∑ j ∈ w.supportY, deltaY A η s0 t j = -deltaOffMassY w η s0 t := by
  have hpart := sum_supportY_add_offSupportY w (fun j ↦ deltaY A η s0 t j)
  rw [sum_deltaY_eq_zero (A := A) η s0 t] at hpart
  rw [deltaOffMassY_eq_sum_deltaY]
  linarith

theorem offMassY_nonneg (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ offMassY w η s0 t := by
  exact Finset.sum_nonneg fun j _ ↦
    nonneg_of_mem_simplex (yIter_mem A η s0 t) j

theorem offMassY_le_one (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    offMassY w η s0 t ≤ 1 := by
  rw [← sum_eq_one_of_mem_simplex (yIter_mem A η s0 t)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ w.offSupportY)
    (fun j _ _ ↦ nonneg_of_mem_simplex (yIter_mem A η s0 t) j)

theorem supportY_card_pos (w : GTWitness A) :
    (0 : ℝ) < w.supportY.card := by
  exact_mod_cast w.supportY_nonempty.card_pos

                                                                 
theorem abs_contrastY_le_sqrtTwo_mul_L (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (s0 : GameState ι κ) (t : ℕ)
    {j : κ} (hj : j ∈ w.offSupportY) :
    |contrastY w η s0 t j| ≤ Real.sqrt 2 * L := by
  have hj' : j ∉ w.supportY := by
    simpa [GTWitness.offSupportY] using hj
  have hc := abs_contrastOn_le w.supportY (A (xIter A η s0 t)) j hj'
    w.supportY_nonempty
  have hu : ‖A (xIter A η s0 t)‖ ≤ L := by
    calc
      ‖A (xIter A η s0 t)‖ ≤ L * ‖xIter A η s0 t‖ :=
        norm_map_le_of_opNorm_le A hA _
      _ ≤ L := by
        simpa using mul_le_mul_of_nonneg_left
          (simplex_norm_le_one (xIter_mem A η s0 t)) hL
  calc
    |contrastY w η s0 t j| ≤
        Real.sqrt (1 + 1 / (w.supportY.card : ℝ)) *
          ‖A (xIter A η s0 t)‖ := hc
    _ ≤ Real.sqrt 2 * L :=
      mul_le_mul (sqrt_one_add_card_inv_le_sqrt_two w.supportY
        w.supportY_nonempty) hu (norm_nonneg _) (Real.sqrt_nonneg _)

                                                                         
theorem abs_storageY_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 ≤ η)
    (s0 : GameState ι κ) (t : ℕ) :
    |storageY w η s0 t| ≤ Real.sqrt 2 * (η * L) := by
  have hynonneg : ∀ j, 0 ≤ yIter A η s0 t j :=
    nonneg_of_mem_simplex (yIter_mem A η s0 t)
  have hterm : ∀ j ∈ w.offSupportY,
      |contrastY w η s0 t j * yIter A η s0 t j| ≤
        (Real.sqrt 2 * L) * yIter A η s0 t j := by
    intro j hj
    rw [abs_mul, abs_of_nonneg (hynonneg j)]
    exact mul_le_mul_of_nonneg_right
      (abs_contrastY_le_sqrtTwo_mul_L w hL hA s0 t hj) (hynonneg j)
  have hsum :
      |∑ j ∈ w.offSupportY,
          contrastY w η s0 t j * yIter A η s0 t j| ≤
        Real.sqrt 2 * L := by
    calc
      |∑ j ∈ w.offSupportY,
          contrastY w η s0 t j * yIter A η s0 t j| ≤
          ∑ j ∈ w.offSupportY,
            |contrastY w η s0 t j * yIter A η s0 t j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ w.offSupportY,
          (Real.sqrt 2 * L) * yIter A η s0 t j :=
        Finset.sum_le_sum hterm
      _ = (Real.sqrt 2 * L) * offMassY w η s0 t := by
        rw [offMassY, Finset.mul_sum]
      _ ≤ Real.sqrt 2 * L := by
        have hc : 0 ≤ Real.sqrt 2 * L :=
          mul_nonneg (Real.sqrt_nonneg _) hL
        simpa using mul_le_mul_of_nonneg_left
          (offMassY_le_one w η s0 t) hc
  rw [storageY, abs_mul, abs_of_nonneg hη]
  calc
    η * |∑ j ∈ w.offSupportY,
        contrastY w η s0 t j * yIter A η s0 t j| ≤
      η * (Real.sqrt 2 * L) := mul_le_mul_of_nonneg_left hsum hη
    _ = Real.sqrt 2 * (η * L) := by ring

                                                                  
theorem reflectedY_coordinate (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) {j : κ} (hj : j ∈ w.offSupportY) :
    deltaY A η s0 t j +
        deltaOffMassY w η s0 t / (w.supportY.card : ℝ) =
      -η * contrastY w η s0 (t + 1) j - η * meanRhoY w η s0 t +
        η * rhoKKT A η s0 t j := by
  have hkkt := congrArg (fun z : EVec κ ↦ z j)
    (deltaY_kkt A hη s0 t)
  simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, ones_apply,
    smul_eq_mul] at hkkt
  simp only [uField] at hkkt
  have hsum := congrArg
    (fun z : EVec κ ↦ ∑ r ∈ w.supportY, z r)
    (deltaY_kkt A hη s0 t)
  simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, ones_apply,
    smul_eq_mul] at hsum
  rw [sum_supportY_deltaY w η s0 t] at hsum
  have hcard : (w.supportY.card : ℝ) ≠ 0 := ne_of_gt (supportY_card_pos w)
  have hsum' :
      -deltaOffMassY w η s0 t =
        η * ((∑ r ∈ w.supportY, uField A η s0 t r) -
          (w.supportY.card : ℝ) * lambdaKKT A η s0 t +
          ∑ r ∈ w.supportY, rhoKKT A η s0 t r) := by
    calc
      -deltaOffMassY w η s0 t =
          ∑ r ∈ w.supportY,
            η * (uField A η s0 t r - lambdaKKT A η s0 t +
              rhoKKT A η s0 t r) := by simpa using hsum
      _ = η * ((∑ r ∈ w.supportY, uField A η s0 t r) -
          (w.supportY.card : ℝ) * lambdaKKT A η s0 t +
          ∑ r ∈ w.supportY, rhoKKT A η s0 t r) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul]
  simp only [uField] at hsum'
  simp only [contrastY, meanRhoY, contrastOn, meanOn]
  ring_nf at hsum' ⊢
  field_simp [hcard, ne_of_gt hη] at hsum' ⊢
  rw [Nat.add_comm t 1] at hkkt
  nlinarith

                                                                            
theorem reflectedY_scalar (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    η * ∑ j ∈ w.offSupportY,
        rhoKKT A η s0 t j * yIter A η s0 t j =
      -(∑ j ∈ w.offSupportY, (deltaY A η s0 t j) ^ 2) -
        (deltaOffMassY w η s0 t) ^ 2 / (w.supportY.card : ℝ) -
        η * ∑ j ∈ w.offSupportY,
          contrastY w η s0 (t + 1) j * deltaY A η s0 t j -
        η * meanRhoY w η s0 t * deltaOffMassY w η s0 t := by
  have hcoord : ∀ j ∈ w.offSupportY,
      deltaY A η s0 t j +
          deltaOffMassY w η s0 t / (w.supportY.card : ℝ) =
        -η * contrastY w η s0 (t + 1) j - η * meanRhoY w η s0 t +
          η * rhoKKT A η s0 t j :=
    fun j hj ↦ reflectedY_coordinate w hη s0 t hj
  have hcomp : ∀ j, rhoKKT A η s0 t j * deltaY A η s0 t j =
      -(rhoKKT A η s0 t j * yIter A η s0 t j) := by
    intro j
    have hc := rhoKKT_complementarity A η s0 t j
    simp only [deltaY, PiLp.sub_apply]
    nlinarith
  have hoff := deltaOffMassY_eq_sum_deltaY w η s0 t
  have hcard : (w.supportY.card : ℝ) ≠ 0 := ne_of_gt (supportY_card_pos w)
  have hcompSum :
      (∑ j ∈ w.offSupportY,
          rhoKKT A η s0 t j * deltaY A η s0 t j) =
        -(∑ j ∈ w.offSupportY,
          rhoKKT A η s0 t j * yIter A η s0 t j) := by
    simp_rw [hcomp]
    rw [Finset.sum_neg_distrib]
  have hweighted :
      ∑ j ∈ w.offSupportY,
          (deltaY A η s0 t j +
              deltaOffMassY w η s0 t / (w.supportY.card : ℝ)) *
            deltaY A η s0 t j =
        ∑ j ∈ w.offSupportY,
          (-η * contrastY w η s0 (t + 1) j - η * meanRhoY w η s0 t +
              η * rhoKKT A η s0 t j) * deltaY A η s0 t j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoord j hj]
  have hleft :
      (∑ j ∈ w.offSupportY,
          (deltaY A η s0 t j +
              deltaOffMassY w η s0 t / (w.supportY.card : ℝ)) *
            deltaY A η s0 t j) =
        (∑ j ∈ w.offSupportY, (deltaY A η s0 t j) ^ 2) +
          (deltaOffMassY w η s0 t) ^ 2 / (w.supportY.card : ℝ) := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hoff]
    field_simp [hcard]
  have hright :
      (∑ j ∈ w.offSupportY,
          (-η * contrastY w η s0 (t + 1) j - η * meanRhoY w η s0 t +
              η * rhoKKT A η s0 t j) * deltaY A η s0 t j) =
        -η * (∑ j ∈ w.offSupportY,
          contrastY w η s0 (t + 1) j * deltaY A η s0 t j) -
        η * meanRhoY w η s0 t * deltaOffMassY w η s0 t +
        η * (∑ j ∈ w.offSupportY,
          rhoKKT A η s0 t j * deltaY A η s0 t j) := by
    have hp : ∀ j : κ,
        (-η * contrastY w η s0 (t + 1) j - η * meanRhoY w η s0 t +
            η * rhoKKT A η s0 t j) * deltaY A η s0 t j =
          (-η) * (contrastY w η s0 (t + 1) j * deltaY A η s0 t j) +
          (-η * meanRhoY w η s0 t) * deltaY A η s0 t j +
          η * (rhoKKT A η s0 t j * deltaY A η s0 t j) := by
      intro j
      ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hoff]
    ring
  rw [hleft, hright, hcompSum] at hweighted
  nlinarith

                                              
theorem storageY_telescope (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    -η * ∑ j ∈ w.offSupportY,
        contrastY w η s0 (t + 1) j * deltaY A η s0 t j =
      storageY w η s0 t - storageY w η s0 (t + 1) +
        η * ∑ j ∈ w.offSupportY,
          (contrastY w η s0 (t + 1) j - contrastY w η s0 t j) *
            yIter A η s0 t j := by
  simp only [storageY, deltaY, PiLp.sub_apply]
  ring_nf
  simp only [Finset.sum_sub_distrib]
  ring

                                                                   
theorem contrastY_drift (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) (j : κ) :
    contrastY w η s0 (t + 1) j - contrastY w η s0 t j =
      contrastOn w.supportY (A (deltaX A η s0 t)) j := by
  rw [contrastY, contrastY, contrastOn_sub]
  congr 1
  simp [deltaX, map_sub]

                                                                          
theorem slackMassY_eq_sum_offSupport (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    slackMassY w η s0 t =
      ∑ j ∈ w.offSupportY, w.slackY j * yIter A η s0 t j := by
  rw [slackMassY, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← sum_supportY_add_offSupportY w
    (fun j ↦ yIter A η s0 t j * w.slackY j)]
  have hs : (∑ j ∈ w.supportY,
      yIter A η s0 t j * w.slackY j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [w.slackY_eq_zero_of_mem_support hj, mul_zero]
  rw [hs, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  ring

                                                                          
theorem equilibriumMultiplierY_eq_sum_support (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    equilibriumMultiplierY w η s0 t =
      ∑ j ∈ w.supportY,
        rhoKKT A η s0 t j * w.yStar j := by
  rw [equilibriumMultiplierY, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← sum_supportY_add_offSupportY w
    (fun j ↦ w.yStar j * rhoKKT A η s0 t j)]
  have ho : (∑ j ∈ w.offSupportY,
      w.yStar j * rhoKKT A η s0 t j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [(w.mem_offSupportY).mp hj, zero_mul]
  rw [ho, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem separation_mul_offMassY_le_slackMassY (w : GTWitness A)
    {L δ η : ℝ} (hb : w.SeparationBounds L δ)
    (s0 : GameState ι κ) (t : ℕ) :
    δ * L * offMassY w η s0 t ≤ slackMassY w η s0 t := by
  rw [offMassY, slackMassY_eq_sum_offSupport]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (hb.mul_L_le_slackY j hj)
    (nonneg_of_mem_simplex (yIter_mem A η s0 t) j)

theorem separation_mul_sum_rho_le_equilibriumMultiplierY (w : GTWitness A)
    {L δ η : ℝ} (hb : w.SeparationBounds L δ) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    δ * (∑ j ∈ w.supportY, rhoKKT A η s0 t j) ≤
      equilibriumMultiplierY w η s0 t := by
  rw [equilibriumMultiplierY_eq_sum_support, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb.le_yStar j hj)
    (rhoKKT_nonneg A hη s0 t j)

                                                                            
theorem cancellationY_exact (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    (∑ j ∈ w.supportY,
        rhoKKT A η s0 t j * yIter A η s0 t j) -
        meanRhoY w η s0 t * deltaOffMassY w η s0 t =
      ∑ j ∈ w.supportY,
        rhoKKT A η s0 t j *
          contrastOn w.supportY (deltaY A η s0 t) j := by
  have hcomp : ∀ j,
      rhoKKT A η s0 t j * yIter A η s0 t j =
        -(rhoKKT A η s0 t j * deltaY A η s0 t j) := by
    intro j
    have hc := rhoKKT_complementarity A η s0 t j
    simp only [deltaY, PiLp.sub_apply]
    nlinarith
  have hmass := sum_supportY_deltaY w η s0 t
  have hcard : (w.supportY.card : ℝ) ≠ 0 := ne_of_gt (supportY_card_pos w)
  simp_rw [hcomp]
  rw [Finset.sum_neg_distrib]
  simp only [meanRhoY, meanOn, contrastOn]
  have hright :
      (∑ j ∈ w.supportY,
        rhoKKT A η s0 t j *
          ((w.supportY.card : ℝ)⁻¹ *
              (∑ r ∈ w.supportY, deltaY A η s0 t r) -
            deltaY A η s0 t j)) =
        ((w.supportY.card : ℝ)⁻¹ *
            (∑ r ∈ w.supportY, deltaY A η s0 t r)) *
          (∑ j ∈ w.supportY, rhoKKT A η s0 t j) -
        ∑ j ∈ w.supportY,
          rhoKKT A η s0 t j * deltaY A η s0 t j := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hright, hmass]
  field_simp [hcard]
  ring

                                                       
theorem abs_contrastY_drift_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) {j : κ} (hj : j ∈ w.offSupportY) :
    |contrastY w η s0 (t + 1) j - contrastY w η s0 t j| ≤
      Real.sqrt 2 * (η * L ^ 2) := by
  rw [contrastY_drift]
  have hj' : j ∉ w.supportY := by
    simpa [GTWitness.offSupportY] using hj
  have hc := abs_contrastOn_le w.supportY (A (deltaX A η s0 t)) j hj'
    w.supportY_nonempty
  have hg : ‖A (deltaX A η s0 t)‖ ≤ η * L ^ 2 := by
    calc
      ‖A (deltaX A η s0 t)‖ ≤ L * ‖deltaX A η s0 t‖ :=
        norm_map_le_of_opNorm_le A hA _
      _ ≤ L * (η * L) :=
        mul_le_mul_of_nonneg_left (deltaX_norm_le A hL hA hη s0 t) hL
      _ = η * L ^ 2 := by ring
  calc
    |contrastOn w.supportY (A (deltaX A η s0 t)) j| ≤
        Real.sqrt (1 + 1 / (w.supportY.card : ℝ)) *
          ‖A (deltaX A η s0 t)‖ := hc
    _ ≤ Real.sqrt 2 * (η * L ^ 2) :=
      mul_le_mul (sqrt_one_add_card_inv_le_sqrt_two w.supportY
        w.supportY_nonempty) hg (norm_nonneg _) (Real.sqrt_nonneg _)

                                                                            
theorem centeredCollisionY_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    (∑ j ∈ w.supportY,
        rhoKKT A η s0 t j *
          contrastOn w.supportY (deltaY A η s0 t) j) ≤
      (η * L) * ∑ j ∈ w.supportY, rhoKKT A η s0 t j := by
  have hcenter : ∀ j ∈ w.supportY,
      contrastOn w.supportY (deltaY A η s0 t) j ≤ η * L := by
    intro j hj
    have habs := abs_contrastOn_le_of_mem w.supportY
      (deltaY A η s0 t) j hj w.supportY_nonempty
    have hfactor := sqrt_one_sub_card_inv_le_one w.supportY
      w.supportY_nonempty
    have hnorm := deltaY_norm_le A hL hA hη s0 t
    calc
      contrastOn w.supportY (deltaY A η s0 t) j ≤
          |contrastOn w.supportY (deltaY A η s0 t) j| := le_abs_self _
      _ ≤ Real.sqrt (1 - 1 / (w.supportY.card : ℝ)) *
          ‖deltaY A η s0 t‖ := habs
      _ ≤ 1 * (η * L) :=
        mul_le_mul hfactor hnorm (norm_nonneg _) zero_le_one
      _ = η * L := one_mul _
  calc
    (∑ j ∈ w.supportY,
        rhoKKT A η s0 t j *
          contrastOn w.supportY (deltaY A η s0 t) j) ≤
      ∑ j ∈ w.supportY, rhoKKT A η s0 t j * (η * L) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hcenter j hj)
          (rhoKKT_nonneg A hη s0 t j)
    _ = (η * L) * ∑ j ∈ w.supportY, rhoKKT A η s0 t j := by
      rw [← Finset.sum_mul]
      ring

                                                                          
theorem inner_rhoKKT_yIter_eq_support_add_offSupport (w : GTWitness A)
    (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t) =
      (∑ j ∈ w.supportY,
        rhoKKT A η s0 t j * yIter A η s0 t j) +
      ∑ j ∈ w.offSupportY,
        rhoKKT A η s0 t j * yIter A η s0 t j := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← sum_supportY_add_offSupportY w
    (fun j ↦ yIter A η s0 t j * rhoKKT A η s0 t j)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

                                                                       
theorem reflectionY_decomposition (w : GTWitness A) { η : ℝ }
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    η * inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t) =
      storageY w η s0 t - storageY w η s0 (t + 1) +
      η * (∑ j ∈ w.offSupportY,
        (contrastY w η s0 (t + 1) j - contrastY w η s0 t j) *
          yIter A η s0 t j) +
      η * (∑ j ∈ w.supportY,
        rhoKKT A η s0 t j *
          contrastOn w.supportY (deltaY A η s0 t) j) -
      ((∑ j ∈ w.offSupportY, (deltaY A η s0 t j) ^ 2) +
        (deltaOffMassY w η s0 t) ^ 2 / (w.supportY.card : ℝ)) := by
  have hpair := inner_rhoKKT_yIter_eq_support_add_offSupport w η s0 t
  have href := reflectedY_scalar w hη s0 t
  have htel := storageY_telescope w η s0 t
  have hcancel := cancellationY_exact w η s0 t
  linear_combination η * hpair + href + htel + η * hcancel

                                                                         
theorem driftCollisionY_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    (∑ j ∈ w.offSupportY,
        (contrastY w η s0 (t + 1) j - contrastY w η s0 t j) *
          yIter A η s0 t j) ≤
      (Real.sqrt 2 * (η * L ^ 2)) * offMassY w η s0 t := by
  calc
    (∑ j ∈ w.offSupportY,
        (contrastY w η s0 (t + 1) j - contrastY w η s0 t j) *
          yIter A η s0 t j) ≤
      ∑ j ∈ w.offSupportY,
        (Real.sqrt 2 * (η * L ^ 2)) * yIter A η s0 t j := by
      apply Finset.sum_le_sum
      intro j hj
      have hcoord :
          contrastY w η s0 (t + 1) j - contrastY w η s0 t j ≤
            Real.sqrt 2 * (η * L ^ 2) :=
        le_trans (le_abs_self _)
          (abs_contrastY_drift_le w hL hA hη s0 t hj)
      exact mul_le_mul_of_nonneg_right hcoord
        (nonneg_of_mem_simplex (yIter_mem A η s0 t) j)
    _ = (Real.sqrt 2 * (η * L ^ 2)) * offMassY w η s0 t := by
      rw [offMassY, Finset.mul_sum]

                                                                          
                                                       
theorem yBlockBound (w : GTWitness A) {L δ η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hb : w.SeparationBounds L δ)
    (hstep : η * L ≤ δ / (2 * Real.sqrt 2))
    (s0 : GameState ι κ) (t : ℕ) :
    η * inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t) ≤
      storageY w η s0 t - storageY w η s0 (t + 1) +
      (η / 2) * slackMassY w η s0 t +
      (η / 2) * equilibriumMultiplierY w η s0 t := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hq : 0 ≤ η * L := mul_nonneg hη.le hL.le
  have hstep' : (η * L) * (2 * Real.sqrt 2) ≤ δ :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)).mp hstep
  have hmass := separation_mul_offMassY_le_slackMassY w ( η := η ) hb s0 t
  have hoff : 0 ≤ L * offMassY w η s0 t :=
    mul_nonneg hL.le (offMassY_nonneg w η s0 t)
  have hscaled := mul_le_mul_of_nonneg_right hstep' hoff
  have hdriftCoeff :
      Real.sqrt 2 * (η * L ^ 2) * offMassY w η s0 t ≤
        slackMassY w η s0 t / 2 := by
    ring_nf at hscaled hmass ⊢
    nlinarith
  have hsumRho : 0 ≤ ∑ j ∈ w.supportY, rhoKKT A η s0 t j :=
    Finset.sum_nonneg fun j _ ↦ rhoKKT_nonneg A hη s0 t j
  have htwo : (2 : ℝ) ≤ 2 * Real.sqrt 2 := by nlinarith
  have htwoq : 2 * (η * L) ≤ (η * L) * (2 * Real.sqrt 2) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left htwo hq
  have hcenterStep : 2 * (η * L) ≤ δ := le_trans htwoq hstep'
  have hcenterScaled := mul_le_mul_of_nonneg_right hcenterStep hsumRho
  have hsepCenter :=
    separation_mul_sum_rho_le_equilibriumMultiplierY w hb hη s0 t
  have hcenterCoeff :
      (η * L) * (∑ j ∈ w.supportY, rhoKKT A η s0 t j) ≤
        equilibriumMultiplierY w η s0 t / 2 := by
    ring_nf at hcenterScaled hsepCenter ⊢
    nlinarith
  have hdrift := driftCollisionY_le w hL.le hA hη s0 t
  have hcenter := centeredCollisionY_le w hL.le hA hη s0 t
  have hquad : 0 ≤
      (∑ j ∈ w.offSupportY, (deltaY A η s0 t j) ^ 2) +
        (deltaOffMassY w η s0 t) ^ 2 / (w.supportY.card : ℝ) := by
    exact add_nonneg (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
      (div_nonneg (sq_nonneg _) (supportY_card_pos w).le)
  rw [reflectionY_decomposition w hη s0 t]
  have hdrift' := mul_le_mul_of_nonneg_left
    (le_trans hdrift hdriftCoeff) hη.le
  have hcenter' := mul_le_mul_of_nonneg_left
    (le_trans hcenter hcenterCoeff) hη.le
  nlinarith

end

end AltGDA
