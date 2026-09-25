import AltGDA.Analysis.SupportGeometry
import AltGDA.Analysis.Energy
import AltGDA.Game.Separation
import AltGDA.Dynamics.KKTData

   
                                          

                                                                             
                                                                            
                                                                           
                                                                       
                                                
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable {A : PayoffOperator ι κ}

                                                                 
def offMassX (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  ∑ i ∈ w.offSupportX, xIter A η s0 t i

                                                    
def deltaOffMassX (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  offMassX w η s0 (t + 1) - offMassX w η s0 t

                                                                               
def contrastX (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) (i : ι) : ℝ :=
  contrastOn w.supportX (vField A η s0 t) i

                                                       
def meanMuX (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  meanOn w.supportX (muKKT A η s0 t)

                                                                            
def previousXContrastTime : ℕ → ℕ
  | 0 => 0
  | t + 1 => t

                                                                              
def storageX (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  η * ∑ i ∈ w.offSupportX,
    contrastX w η s0 (previousXContrastTime t) i * xIter A η s0 t i

@[simp]
theorem previousXContrastTime_zero : previousXContrastTime 0 = 0 := rfl

@[simp]
theorem previousXContrastTime_succ (t : ℕ) :
    previousXContrastTime (t + 1) = t := rfl

                                                                  
theorem sum_supportX_add_offSupportX (w : GTWitness A) (f : ι → ℝ) :
    (∑ i ∈ w.supportX, f i) + (∑ i ∈ w.offSupportX, f i) = ∑ i, f i := by
  classical
  rw [GTWitness.offSupportX]
  rw [add_comm, Finset.sum_sdiff (Finset.subset_univ w.supportX)]

                                                                    
theorem sum_deltaX_eq_zero (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    ∑ i, deltaX A η s0 t i = 0 := by
  simp [deltaX, Finset.sum_sub_distrib,
    sum_eq_one_of_mem_simplex (xIter_mem A η s0 (t + 1)),
    sum_eq_one_of_mem_simplex (xIter_mem A η s0 t)]

                                                                          
theorem deltaOffMassX_eq_sum_deltaX (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    deltaOffMassX w η s0 t = ∑ i ∈ w.offSupportX, deltaX A η s0 t i := by
  simp [deltaOffMassX, offMassX, deltaX, Finset.sum_sub_distrib]

                                                                       
theorem sum_supportX_deltaX (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    ∑ i ∈ w.supportX, deltaX A η s0 t i = -deltaOffMassX w η s0 t := by
  have hpart := sum_supportX_add_offSupportX w (fun i ↦ deltaX A η s0 t i)
  rw [sum_deltaX_eq_zero (A := A) η s0 t] at hpart
  rw [deltaOffMassX_eq_sum_deltaX]
  linarith

                                       
theorem offMassX_nonneg (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ offMassX w η s0 t := by
  exact Finset.sum_nonneg fun i _ ↦
    nonneg_of_mem_simplex (xIter_mem A η s0 t) i

                                                             
theorem offMassX_le_one (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    offMassX w η s0 t ≤ 1 := by
  rw [← sum_eq_one_of_mem_simplex (xIter_mem A η s0 t)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ w.offSupportX)
    (fun i _ _ ↦ nonneg_of_mem_simplex (xIter_mem A η s0 t) i)

                                                                     
theorem supportX_card_pos (w : GTWitness A) :
    (0 : ℝ) < w.supportX.card := by
  exact_mod_cast w.supportX_nonempty.card_pos

                                                              
theorem sqrt_one_add_card_inv_le_sqrt_two (S : Finset ι) (hS : S.Nonempty) :
    Real.sqrt (1 + 1 / (S.card : ℝ)) ≤ Real.sqrt 2 := by
  apply Real.sqrt_le_sqrt
  have hk : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  have hkpos : (0 : ℝ) < S.card := lt_of_lt_of_le zero_lt_one hk
  have hinv : (1 : ℝ) / S.card ≤ 1 := (div_le_one hkpos).2 hk
  linarith

                                                           
theorem sqrt_one_sub_card_inv_le_one (S : Finset ι) (hS : S.Nonempty) :
    Real.sqrt (1 - 1 / (S.card : ℝ)) ≤ 1 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · have hkpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hinv : 0 ≤ (1 : ℝ) / S.card := div_nonneg zero_le_one hkpos.le
    nlinarith

                                                                 
theorem abs_contrastX_le_sqrtTwo_mul_L (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (s0 : GameState ι κ) (t : ℕ)
    {i : ι} (hi : i ∈ w.offSupportX) :
    |contrastX w η s0 t i| ≤ Real.sqrt 2 * L := by
  have hi' : i ∉ w.supportX := by
    simpa [GTWitness.offSupportX] using hi
  have hc := abs_contrastOn_le w.supportX (vField A η s0 t) i hi'
    w.supportX_nonempty
  have hv : ‖vField A η s0 t‖ ≤ L := by
    calc
      ‖vField A η s0 t‖ = ‖payoffAdjoint A (yIter A η s0 t)‖ := by
        simp [vField]
      _ ≤ L * ‖yIter A η s0 t‖ :=
        norm_adjoint_map_le_of_opNorm_le A hA _
      _ ≤ L := by
        simpa using mul_le_mul_of_nonneg_left
          (simplex_norm_le_one (yIter_mem A η s0 t)) hL
  calc
    |contrastX w η s0 t i| ≤
        Real.sqrt (1 + 1 / (w.supportX.card : ℝ)) *
          ‖vField A η s0 t‖ := hc
    _ ≤ Real.sqrt 2 * L :=
      mul_le_mul (sqrt_one_add_card_inv_le_sqrt_two w.supportX
        w.supportX_nonempty) hv (norm_nonneg _) (Real.sqrt_nonneg _)

                                                                         
theorem abs_storageX_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 ≤ η)
    (s0 : GameState ι κ) (t : ℕ) :
    |storageX w η s0 t| ≤ Real.sqrt 2 * (η * L) := by
  have hxnonneg : ∀ i, 0 ≤ xIter A η s0 t i :=
    nonneg_of_mem_simplex (xIter_mem A η s0 t)
  have hterm : ∀ i ∈ w.offSupportX,
      |contrastX w η s0 (previousXContrastTime t) i *
          xIter A η s0 t i| ≤
        (Real.sqrt 2 * L) * xIter A η s0 t i := by
    intro i hi
    rw [abs_mul, abs_of_nonneg (hxnonneg i)]
    exact mul_le_mul_of_nonneg_right
      (abs_contrastX_le_sqrtTwo_mul_L w hL hA s0
        (previousXContrastTime t) hi) (hxnonneg i)
  have hsum :
      |∑ i ∈ w.offSupportX,
          contrastX w η s0 (previousXContrastTime t) i *
            xIter A η s0 t i| ≤ Real.sqrt 2 * L := by
    calc
      |∑ i ∈ w.offSupportX,
          contrastX w η s0 (previousXContrastTime t) i *
            xIter A η s0 t i| ≤
          ∑ i ∈ w.offSupportX,
            |contrastX w η s0 (previousXContrastTime t) i *
              xIter A η s0 t i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ w.offSupportX,
          (Real.sqrt 2 * L) * xIter A η s0 t i :=
        Finset.sum_le_sum hterm
      _ = (Real.sqrt 2 * L) * offMassX w η s0 t := by
        rw [offMassX, Finset.mul_sum]
      _ ≤ Real.sqrt 2 * L := by
        have hc : 0 ≤ Real.sqrt 2 * L :=
          mul_nonneg (Real.sqrt_nonneg _) hL
        simpa using mul_le_mul_of_nonneg_left
          (offMassX_le_one w η s0 t) hc
  rw [storageX, abs_mul, abs_of_nonneg hη]
  calc
    η * |∑ i ∈ w.offSupportX,
        contrastX w η s0 (previousXContrastTime t) i *
          xIter A η s0 t i| ≤ η * (Real.sqrt 2 * L) :=
      mul_le_mul_of_nonneg_left hsum hη
    _ = Real.sqrt 2 * (η * L) := by ring

                                                                  
theorem reflectedX_coordinate (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) {i : ι} (hi : i ∈ w.offSupportX) :
    deltaX A η s0 t i +
        deltaOffMassX w η s0 t / (w.supportX.card : ℝ) =
      -η * contrastX w η s0 t i - η * meanMuX w η s0 t +
        η * muKKT A η s0 t i := by
  have hkkt := congrArg (fun z : EVec ι ↦ z i)
    (deltaX_kkt A hη s0 t)
  simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, ones_apply,
    smul_eq_mul] at hkkt
  have hsum := congrArg
    (fun z : EVec ι ↦ ∑ j ∈ w.supportX, z j)
    (deltaX_kkt A hη s0 t)
  simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, ones_apply,
    smul_eq_mul] at hsum
  rw [sum_supportX_deltaX w η s0 t] at hsum
  have hcard : (w.supportX.card : ℝ) ≠ 0 := ne_of_gt (supportX_card_pos w)
  have hsum' :
      -deltaOffMassX w η s0 t =
        η * ((∑ j ∈ w.supportX, vField A η s0 t j) -
          (w.supportX.card : ℝ) * gammaKKT A η s0 t +
          ∑ j ∈ w.supportX, muKKT A η s0 t j) := by
    calc
      -deltaOffMassX w η s0 t =
          ∑ j ∈ w.supportX,
            η * (vField A η s0 t j - gammaKKT A η s0 t +
              muKKT A η s0 t j) := by simpa using hsum
      _ = η * ((∑ j ∈ w.supportX, vField A η s0 t j) -
          (w.supportX.card : ℝ) * gammaKKT A η s0 t +
          ∑ j ∈ w.supportX, muKKT A η s0 t j) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul]
  simp only [contrastX, meanMuX, contrastOn, meanOn]
  ring_nf at hsum' ⊢
  field_simp [hcard, ne_of_gt hη] at hsum' ⊢
  nlinarith

                                                                            
theorem reflectedX_scalar (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    η * ∑ i ∈ w.offSupportX,
        muKKT A η s0 t i * xIter A η s0 t i =
      -(∑ i ∈ w.offSupportX, (deltaX A η s0 t i) ^ 2) -
        (deltaOffMassX w η s0 t) ^ 2 / (w.supportX.card : ℝ) -
        η * ∑ i ∈ w.offSupportX,
          contrastX w η s0 t i * deltaX A η s0 t i -
        η * meanMuX w η s0 t * deltaOffMassX w η s0 t := by
  have hcoord : ∀ i ∈ w.offSupportX,
      deltaX A η s0 t i +
          deltaOffMassX w η s0 t / (w.supportX.card : ℝ) =
        -η * contrastX w η s0 t i - η * meanMuX w η s0 t +
          η * muKKT A η s0 t i :=
    fun i hi ↦ reflectedX_coordinate w hη s0 t hi
  have hcomp : ∀ i, muKKT A η s0 t i * deltaX A η s0 t i =
      -(muKKT A η s0 t i * xIter A η s0 t i) := by
    intro i
    have hc := muKKT_complementarity A η s0 t i
    simp only [deltaX, PiLp.sub_apply]
    nlinarith
  have hoff := deltaOffMassX_eq_sum_deltaX w η s0 t
  have hcard : (w.supportX.card : ℝ) ≠ 0 := ne_of_gt (supportX_card_pos w)
  have hcompSum :
      (∑ i ∈ w.offSupportX,
          muKKT A η s0 t i * deltaX A η s0 t i) =
        -(∑ i ∈ w.offSupportX,
          muKKT A η s0 t i * xIter A η s0 t i) := by
    simp_rw [hcomp]
    rw [Finset.sum_neg_distrib]
                                                                       
  have hweighted :
      ∑ i ∈ w.offSupportX,
          (deltaX A η s0 t i +
              deltaOffMassX w η s0 t / (w.supportX.card : ℝ)) *
            deltaX A η s0 t i =
        ∑ i ∈ w.offSupportX,
          (-η * contrastX w η s0 t i - η * meanMuX w η s0 t +
              η * muKKT A η s0 t i) * deltaX A η s0 t i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord i hi]
  have hleft :
      (∑ i ∈ w.offSupportX,
          (deltaX A η s0 t i +
              deltaOffMassX w η s0 t / (w.supportX.card : ℝ)) *
            deltaX A η s0 t i) =
        (∑ i ∈ w.offSupportX, (deltaX A η s0 t i) ^ 2) +
          (deltaOffMassX w η s0 t) ^ 2 / (w.supportX.card : ℝ) := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hoff]
    field_simp [hcard]
  have hright :
      (∑ i ∈ w.offSupportX,
          (-η * contrastX w η s0 t i - η * meanMuX w η s0 t +
              η * muKKT A η s0 t i) * deltaX A η s0 t i) =
        -η * (∑ i ∈ w.offSupportX,
          contrastX w η s0 t i * deltaX A η s0 t i) -
        η * meanMuX w η s0 t * deltaOffMassX w η s0 t +
        η * (∑ i ∈ w.offSupportX,
          muKKT A η s0 t i * deltaX A η s0 t i) := by
    have hp : ∀ i : ι,
        (-η * contrastX w η s0 t i - η * meanMuX w η s0 t +
            η * muKKT A η s0 t i) * deltaX A η s0 t i =
          (-η) * (contrastX w η s0 t i * deltaX A η s0 t i) +
          (-η * meanMuX w η s0 t) * deltaX A η s0 t i +
          η * (muKKT A η s0 t i * deltaX A η s0 t i) := by
      intro i
      ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hoff]
    ring
  rw [hleft, hright, hcompSum] at hweighted
  nlinarith

                                                                             
theorem storageX_telescope (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    -η * ∑ i ∈ w.offSupportX,
        contrastX w η s0 t i * deltaX A η s0 t i =
      storageX w η s0 t - storageX w η s0 (t + 1) +
        η * ∑ i ∈ w.offSupportX,
          (contrastX w η s0 t i -
              contrastX w η s0 (previousXContrastTime t) i) *
            xIter A η s0 t i := by
  simp only [storageX, previousXContrastTime_succ, deltaX, PiLp.sub_apply]
  ring_nf
  simp only [Finset.sum_sub_distrib]
  ring

                                                                           
@[simp]
theorem contrastX_sub_previous_zero (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (i : ι) :
    contrastX w η s0 0 i -
        contrastX w η s0 (previousXContrastTime 0) i = 0 := by
  simp [previousXContrastTime]

                                            
theorem contrastOn_sub (S : Finset ι) (g h : EVec ι) (i : ι) :
    contrastOn S g i - contrastOn S h i = contrastOn S (g - h) i := by
  simp only [contrastOn, meanOn, PiLp.sub_apply, Finset.sum_sub_distrib]
  ring

                                                                      
theorem contrastX_drift_succ (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) (i : ι) :
    contrastX w η s0 (t + 1) i - contrastX w η s0 t i =
      contrastOn w.supportX
        (-payoffAdjoint A (deltaY A η s0 t)) i := by
  rw [contrastX, contrastX, contrastOn_sub]
  congr 1
  simp only [vField, deltaY, map_sub]
  module

                                                                          
theorem slackMassX_eq_sum_offSupport (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    slackMassX w η s0 t =
      ∑ i ∈ w.offSupportX, w.slackX i * xIter A η s0 t i := by
  rw [slackMassX, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← sum_supportX_add_offSupportX w
    (fun i ↦ xIter A η s0 t i * w.slackX i)]
  have hs : (∑ i ∈ w.supportX,
      xIter A η s0 t i * w.slackX i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [w.slackX_eq_zero_of_mem_support hi, mul_zero]
  rw [hs, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

                                                                        
theorem equilibriumMultiplierX_eq_sum_support (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    equilibriumMultiplierX w η s0 t =
      ∑ i ∈ w.supportX,
        muKKT A η s0 t i * w.xStar i := by
  rw [equilibriumMultiplierX, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← sum_supportX_add_offSupportX w
    (fun i ↦ w.xStar i * muKKT A η s0 t i)]
  have ho : (∑ i ∈ w.offSupportX,
      w.xStar i * muKKT A η s0 t i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [(w.mem_offSupportX).mp hi, zero_mul]
  rw [ho, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

                                                                      
theorem separation_mul_offMassX_le_slackMassX (w : GTWitness A)
    {L δ η : ℝ} (hb : w.SeparationBounds L δ)
    (s0 : GameState ι κ) (t : ℕ) :
    δ * L * offMassX w η s0 t ≤ slackMassX w η s0 t := by
  rw [offMassX, slackMassX_eq_sum_offSupport]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (hb.mul_L_le_slackX i hi)
    (nonneg_of_mem_simplex (xIter_mem A η s0 t) i)

                                                                   
theorem separation_mul_sum_mu_le_equilibriumMultiplierX (w : GTWitness A)
    {L δ η : ℝ} (hb : w.SeparationBounds L δ) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    δ * (∑ i ∈ w.supportX, muKKT A η s0 t i) ≤
      equilibriumMultiplierX w η s0 t := by
  rw [equilibriumMultiplierX_eq_sum_support, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb.le_xStar i hi)
    (muKKT_nonneg A hη s0 t i)

                                                    
theorem cancellationX_exact (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    (∑ i ∈ w.supportX,
        muKKT A η s0 t i * xIter A η s0 t i) -
        meanMuX w η s0 t * deltaOffMassX w η s0 t =
      ∑ i ∈ w.supportX,
        muKKT A η s0 t i *
          contrastOn w.supportX (deltaX A η s0 t) i := by
  have hcomp : ∀ i,
      muKKT A η s0 t i * xIter A η s0 t i =
        -(muKKT A η s0 t i * deltaX A η s0 t i) := by
    intro i
    have hc := muKKT_complementarity A η s0 t i
    simp only [deltaX, PiLp.sub_apply]
    nlinarith
  have hmass := sum_supportX_deltaX w η s0 t
  have hcard : (w.supportX.card : ℝ) ≠ 0 := ne_of_gt (supportX_card_pos w)
  simp_rw [hcomp]
  rw [Finset.sum_neg_distrib]
  simp only [meanMuX, meanOn, contrastOn]
  have hright :
      (∑ i ∈ w.supportX,
        muKKT A η s0 t i *
          ((w.supportX.card : ℝ)⁻¹ *
              (∑ j ∈ w.supportX, deltaX A η s0 t j) -
            deltaX A η s0 t i)) =
        ((w.supportX.card : ℝ)⁻¹ *
            (∑ j ∈ w.supportX, deltaX A η s0 t j)) *
          (∑ i ∈ w.supportX, muKKT A η s0 t i) -
        ∑ i ∈ w.supportX,
          muKKT A η s0 t i * deltaX A η s0 t i := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hright, hmass]
  field_simp [hcard]
  ring

                                                                                   
theorem abs_contrastX_drift_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) {i : ι} (hi : i ∈ w.offSupportX) :
    |contrastX w η s0 t i -
        contrastX w η s0 (previousXContrastTime t) i| ≤
      Real.sqrt 2 * (η * L ^ 2) := by
  cases t with
  | zero =>
      simp [previousXContrastTime]
      positivity
  | succ t =>
      rw [previousXContrastTime_succ, contrastX_drift_succ]
      have hi' : i ∉ w.supportX := by
        simpa [GTWitness.offSupportX] using hi
      have hc := abs_contrastOn_le w.supportX
        (-payoffAdjoint A (deltaY A η s0 t)) i hi' w.supportX_nonempty
      have hg : ‖-payoffAdjoint A (deltaY A η s0 t)‖ ≤ η * L ^ 2 := by
        calc
          ‖-payoffAdjoint A (deltaY A η s0 t)‖ =
              ‖payoffAdjoint A (deltaY A η s0 t)‖ := norm_neg _
          _ ≤ L * ‖deltaY A η s0 t‖ :=
            norm_adjoint_map_le_of_opNorm_le A hA _
          _ ≤ L * (η * L) :=
            mul_le_mul_of_nonneg_left
              (deltaY_norm_le A hL hA hη s0 t) hL
          _ = η * L ^ 2 := by ring
      calc
        |contrastOn w.supportX
            (-payoffAdjoint A (deltaY A η s0 t)) i| ≤
          Real.sqrt (1 + 1 / (w.supportX.card : ℝ)) *
            ‖-payoffAdjoint A (deltaY A η s0 t)‖ := hc
        _ ≤ Real.sqrt 2 * (η * L ^ 2) :=
          mul_le_mul (sqrt_one_add_card_inv_le_sqrt_two w.supportX
            w.supportX_nonempty) hg (norm_nonneg _) (Real.sqrt_nonneg _)

                                                                            
theorem centeredCollisionX_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    (∑ i ∈ w.supportX,
        muKKT A η s0 t i *
          contrastOn w.supportX (deltaX A η s0 t) i) ≤
      (η * L) * ∑ i ∈ w.supportX, muKKT A η s0 t i := by
  have hcenter : ∀ i ∈ w.supportX,
      contrastOn w.supportX (deltaX A η s0 t) i ≤ η * L := by
    intro i hi
    have habs := abs_contrastOn_le_of_mem w.supportX
      (deltaX A η s0 t) i hi w.supportX_nonempty
    have hfactor := sqrt_one_sub_card_inv_le_one w.supportX
      w.supportX_nonempty
    have hnorm := deltaX_norm_le A hL hA hη s0 t
    have hc_le_abs : contrastOn w.supportX (deltaX A η s0 t) i ≤
        |contrastOn w.supportX (deltaX A η s0 t) i| := le_abs_self _
    calc
      contrastOn w.supportX (deltaX A η s0 t) i ≤
          |contrastOn w.supportX (deltaX A η s0 t) i| := hc_le_abs
      _ ≤ Real.sqrt (1 - 1 / (w.supportX.card : ℝ)) *
          ‖deltaX A η s0 t‖ := habs
      _ ≤ 1 * (η * L) :=
        mul_le_mul hfactor hnorm (norm_nonneg _) zero_le_one
      _ = η * L := one_mul _
  calc
    (∑ i ∈ w.supportX,
        muKKT A η s0 t i *
          contrastOn w.supportX (deltaX A η s0 t) i) ≤
      ∑ i ∈ w.supportX, muKKT A η s0 t i * (η * L) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hcenter i hi)
          (muKKT_nonneg A hη s0 t i)
    _ = (η * L) * ∑ i ∈ w.supportX, muKKT A η s0 t i := by
      rw [← Finset.sum_mul]
      ring

                                                                          
theorem inner_muKKT_xIter_eq_support_add_offSupport (w : GTWitness A)
    (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    inner ℝ (muKKT A η s0 t) (xIter A η s0 t) =
      (∑ i ∈ w.supportX,
        muKKT A η s0 t i * xIter A η s0 t i) +
      ∑ i ∈ w.offSupportX,
        muKKT A η s0 t i * xIter A η s0 t i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← sum_supportX_add_offSupportX w
    (fun i ↦ xIter A η s0 t i * muKKT A η s0 t i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

                                                            

                                                                      
                                                               
                                                                   
  
theorem reflectionX_decomposition (w : GTWitness A) { η : ℝ }
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    η * inner ℝ (muKKT A η s0 t) (xIter A η s0 t) =
      storageX w η s0 t - storageX w η s0 (t + 1) +
      η * (∑ i ∈ w.offSupportX,
        (contrastX w η s0 t i -
          contrastX w η s0 (previousXContrastTime t) i) *
          xIter A η s0 t i) +
      η * (∑ i ∈ w.supportX,
        muKKT A η s0 t i *
          contrastOn w.supportX (deltaX A η s0 t) i) -
      ((∑ i ∈ w.offSupportX, (deltaX A η s0 t i) ^ 2) +
        (deltaOffMassX w η s0 t) ^ 2 / (w.supportX.card : ℝ)) := by
  have hpair := inner_muKKT_xIter_eq_support_add_offSupport w η s0 t
  have href := reflectedX_scalar w hη s0 t
  have htel := storageX_telescope w η s0 t
  have hcancel := cancellationX_exact w η s0 t
  linear_combination η * hpair + href + htel + η * hcancel

                                                                       
theorem driftCollisionX_le (w : GTWitness A) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    (∑ i ∈ w.offSupportX,
        (contrastX w η s0 t i -
          contrastX w η s0 (previousXContrastTime t) i) *
          xIter A η s0 t i) ≤
      (Real.sqrt 2 * (η * L ^ 2)) * offMassX w η s0 t := by
  calc
    (∑ i ∈ w.offSupportX,
        (contrastX w η s0 t i -
          contrastX w η s0 (previousXContrastTime t) i) *
          xIter A η s0 t i) ≤
      ∑ i ∈ w.offSupportX,
        (Real.sqrt 2 * (η * L ^ 2)) * xIter A η s0 t i := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoord :
          contrastX w η s0 t i -
              contrastX w η s0 (previousXContrastTime t) i ≤
            Real.sqrt 2 * (η * L ^ 2) :=
        le_trans (le_abs_self _)
          (abs_contrastX_drift_le w hL hA hη s0 t hi)
      exact mul_le_mul_of_nonneg_right hcoord
        (nonneg_of_mem_simplex (xIter_mem A η s0 t) i)
    _ = (Real.sqrt 2 * (η * L ^ 2)) * offMassX w η s0 t := by
      rw [offMassX, Finset.mul_sum]

                                                                      
                                                   
theorem xBlockBound (w : GTWitness A) {L δ η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (hb : w.SeparationBounds L δ)
    (hstep : η * L ≤ δ / (2 * Real.sqrt 2))
    (s0 : GameState ι κ) (t : ℕ) :
    η * inner ℝ (muKKT A η s0 t) (xIter A η s0 t) ≤
      storageX w η s0 t - storageX w η s0 (t + 1) +
      (η / 2) * slackMassX w η s0 t +
      (η / 2) * equilibriumMultiplierX w η s0 t := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hq : 0 ≤ η * L := mul_nonneg hη.le hL.le
  have hstep' : (η * L) * (2 * Real.sqrt 2) ≤ δ :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)).mp hstep
  have hmass := separation_mul_offMassX_le_slackMassX w ( η := η ) hb s0 t
  have hoff : 0 ≤ L * offMassX w η s0 t :=
    mul_nonneg hL.le (offMassX_nonneg w η s0 t)
  have hscaled := mul_le_mul_of_nonneg_right hstep' hoff
  have hdriftCoeff :
      Real.sqrt 2 * (η * L ^ 2) * offMassX w η s0 t ≤
        slackMassX w η s0 t / 2 := by
    ring_nf at hscaled hmass ⊢
    nlinarith
  have hsumMu : 0 ≤ ∑ i ∈ w.supportX, muKKT A η s0 t i :=
    Finset.sum_nonneg fun i _ ↦ muKKT_nonneg A hη s0 t i
  have htwo : (2 : ℝ) ≤ 2 * Real.sqrt 2 := by nlinarith
  have htwoq : 2 * (η * L) ≤ (η * L) * (2 * Real.sqrt 2) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left htwo hq
  have hcenterStep : 2 * (η * L) ≤ δ := le_trans htwoq hstep'
  have hcenterScaled := mul_le_mul_of_nonneg_right hcenterStep hsumMu
  have hsepCenter :=
    separation_mul_sum_mu_le_equilibriumMultiplierX w hb hη s0 t
  have hcenterCoeff :
      (η * L) * (∑ i ∈ w.supportX, muKKT A η s0 t i) ≤
        equilibriumMultiplierX w η s0 t / 2 := by
    ring_nf at hcenterScaled hsepCenter ⊢
    nlinarith
  have hdrift := driftCollisionX_le w hL.le hA hη s0 t
  have hcenter := centeredCollisionX_le w hL.le hA hη s0 t
  have hquad : 0 ≤
      (∑ i ∈ w.offSupportX, (deltaX A η s0 t i) ^ 2) +
        (deltaOffMassX w η s0 t) ^ 2 / (w.supportX.card : ℝ) := by
    exact add_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
      (div_nonneg (sq_nonneg _) (supportX_card_pos w).le)
  rw [reflectionX_decomposition w hη s0 t]
  have hdrift' := mul_le_mul_of_nonneg_left
    (le_trans hdrift hdriftCoeff) hη.le
  have hcenter' := mul_le_mul_of_nonneg_left
    (le_trans hcenter hcenterCoeff) hη.le
  nlinarith

end

end AltGDA
