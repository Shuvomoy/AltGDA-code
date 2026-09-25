import AltGDA.Analysis.Residual
import AltGDA.Game.Separation

   
                              

                                                                         
                                                                    
                               
  

open scoped BigOperators RealInnerProductSpace InnerProduct

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable {A : PayoffOperator ι κ}

                                                                 
def slackMassX (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  inner ℝ w.slackX (xIter A η s0 t)

                                                                 
def slackMassY (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  inner ℝ w.slackY (yIter A η s0 t)

                         
def slackMass (w : GTWitness A) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  slackMassX w η s0 t + slackMassY w η s0 t

                                                                   
def equilibriumMultiplierX (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  inner ℝ (muKKT A η s0 t) w.xStar

                                                                    
def equilibriumMultiplierY (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  inner ℝ (rhoKKT A η s0 t) w.yStar

                         
def equilibriumMultiplier (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  equilibriumMultiplierX w η s0 t + equilibriumMultiplierY w η s0 t

                                                     
def dissipation (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  η * (slackMass w η s0 t + slackMass w η s0 (t + 1)) +
    2 * η * equilibriumMultiplier w η s0 t

                                                                   
def energy (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  ‖xIter A η s0 t - w.xStar‖ ^ 2 +
    ‖yIter A η s0 t - w.yStar‖ ^ 2 -
      η * payoff A (xIter A η s0 t - w.xStar)
        (yIter A η s0 t - w.yStar)

private theorem inner_nonneg_of_coordinatewise {α : Type*}
    [Fintype α] [DecidableEq α]
    (a b : EVec α) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ inner ℝ a b := by
  rw [PiLp.inner_apply]
  apply Finset.sum_nonneg
  intro i _
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_nonneg (hb i) (ha i)

theorem slackMassX_nonneg (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ slackMassX w η s0 t := by
  exact inner_nonneg_of_coordinatewise _ _ w.slackX_nonneg
    (nonneg_of_mem_simplex (xIter_mem A η s0 t))

theorem slackMassY_nonneg (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ slackMassY w η s0 t := by
  exact inner_nonneg_of_coordinatewise _ _ w.slackY_nonneg
    (nonneg_of_mem_simplex (yIter_mem A η s0 t))

theorem slackMass_nonneg (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ slackMass w η s0 t :=
  add_nonneg (slackMassX_nonneg w η s0 t) (slackMassY_nonneg w η s0 t)

theorem equilibriumMultiplierX_nonneg (w : GTWitness A) {η : ℝ}
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ equilibriumMultiplierX w η s0 t := by
  exact inner_nonneg_of_coordinatewise _ _ (muKKT_nonneg A hη s0 t)
    (nonneg_of_mem_simplex w.x_mem)

theorem equilibriumMultiplierY_nonneg (w : GTWitness A) {η : ℝ}
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ equilibriumMultiplierY w η s0 t := by
  exact inner_nonneg_of_coordinatewise _ _ (rhoKKT_nonneg A hη s0 t)
    (nonneg_of_mem_simplex w.y_mem)

theorem equilibriumMultiplier_nonneg (w : GTWitness A) {η : ℝ}
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ equilibriumMultiplier w η s0 t :=
  add_nonneg (equilibriumMultiplierX_nonneg w hη s0 t)
    (equilibriumMultiplierY_nonneg w hη s0 t)

theorem dissipation_nonneg (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ dissipation w η s0 t := by
  unfold dissipation
  exact add_nonneg
    (mul_nonneg hη.le
      (add_nonneg (slackMass_nonneg w η s0 t)
        (slackMass_nonneg w η s0 (t + 1))))
    (mul_nonneg (mul_nonneg (by norm_num) hη.le)
      (equilibriumMultiplier_nonneg w hη s0 t))

private theorem inner_ones_sub_simplex_eq_zero {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {x z : EVec α} (hx : x ∈ simplex α) (hz : z ∈ simplex α) :
    inner ℝ (ones α) (x - z) = 0 := by
  rw [PiLp.inner_apply]
  simp only [ones_apply, RCLike.inner_apply, conj_trivial, mul_one,
    PiLp.sub_apply, Finset.sum_sub_distrib, sum_eq_one_of_mem_simplex hx,
    sum_eq_one_of_mem_simplex hz, sub_self]

private theorem inner_slackX_xStar_eq_zero (w : GTWitness A) :
    inner ℝ w.slackX w.xStar = 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  apply Finset.sum_eq_zero
  intro i _
  exact w.x_mul_slackX i

private theorem inner_slackY_yStar_eq_zero (w : GTWitness A) :
    inner ℝ w.slackY w.yStar = 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  apply Finset.sum_eq_zero
  intro j _
  exact w.y_mul_slackY j

                                                                                 
theorem payoff_sub_witness_right (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    payoff A (xIter A η s0 t - w.xStar) w.yStar =
      slackMassX w η s0 t := by
  rw [payoff_eq_inner_adjoint, w.adjoint_eq_value_ones_add_slackX]
  simp only [inner_add_right, real_inner_smul_right]
  have hsum := inner_ones_sub_simplex_eq_zero
    (xIter_mem A η s0 t) w.x_mem
  have hsum' : inner ℝ (xIter A η s0 t - w.xStar) (ones ι) = 0 := by
    rw [real_inner_comm]
    exact hsum
  have hstar := inner_slackX_xStar_eq_zero w
  have hstar' : inner ℝ w.xStar w.slackX = 0 := by
    rw [real_inner_comm]
    exact hstar
  rw [hsum', mul_zero, zero_add, inner_sub_left, hstar', sub_zero]
  rw [real_inner_comm]
  rfl

                                                                                     
theorem payoff_witness_left_sub (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    payoff A w.xStar (yIter A η s0 t - w.yStar) =
      -slackMassY w η s0 t := by
  rw [payoff, w.map_eq_value_ones_sub_slackY]
  simp only [inner_sub_left, real_inner_smul_left]
  have hsum := inner_ones_sub_simplex_eq_zero
    (yIter_mem A η s0 t) w.y_mem
  have hstar := inner_slackY_yStar_eq_zero w
  rw [hsum, mul_zero, zero_sub, inner_sub_right, hstar, sub_zero]
  rfl

private theorem energy_inner_x (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    inner ℝ (xIter A η s0 t - w.xStar) (deltaX A η s0 t) =
      -η * slackMassX w η s0 t -
        η * payoff A (xIter A η s0 t - w.xStar)
          (yIter A η s0 t - w.yStar) +
        η * inner ℝ (muKKT A η s0 t)
          (xIter A η s0 t - w.xStar) := by
  let a := xIter A η s0 t - w.xStar
  have hsum : inner ℝ a (ones ι) = 0 := by
    rw [real_inner_comm]
    exact inner_ones_sub_simplex_eq_zero (xIter_mem A η s0 t) w.x_mem
  have hkkt := deltaX_kkt A hη s0 t
  have hv : inner ℝ a (vField A η s0 t) =
      -slackMassX w η s0 t -
        payoff A a (yIter A η s0 t - w.yStar) := by
    calc
      inner ℝ a (vField A η s0 t) =
          -payoff A a (yIter A η s0 t) := by
        rw [payoff_eq_inner_adjoint]
        simp [vField]
      _ = -(payoff A a w.yStar +
          payoff A a (yIter A η s0 t - w.yStar)) := by
        congr 1
        rw [← payoff_add_right]
        congr 2
        abel
      _ = -slackMassX w η s0 t -
          payoff A a (yIter A η s0 t - w.yStar) := by
        rw [payoff_sub_witness_right]
        ring
  change inner ℝ a (deltaX A η s0 t) =
    -η * slackMassX w η s0 t -
      η * payoff A a (yIter A η s0 t - w.yStar) +
      η * inner ℝ (muKKT A η s0 t) a
  rw [hkkt]
  simp only [real_inner_smul_right, inner_add_right, inner_sub_right,
    real_inner_smul_right]
  rw [hsum, mul_zero, sub_zero, hv,
    real_inner_comm (x := a) (y := muKKT A η s0 t)]
  ring

private theorem energy_inner_y (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    inner ℝ (yIter A η s0 t - w.yStar) (deltaY A η s0 t) =
      -η * slackMassY w η s0 t +
        η * payoff A (xIter A η s0 t - w.xStar)
          (yIter A η s0 t - w.yStar) +
        η * payoff A (deltaX A η s0 t)
          (yIter A η s0 t - w.yStar) +
        η * inner ℝ (rhoKKT A η s0 t)
          (yIter A η s0 t - w.yStar) := by
  let b := yIter A η s0 t - w.yStar
  have hsum : inner ℝ b (ones κ) = 0 := by
    rw [real_inner_comm]
    exact inner_ones_sub_simplex_eq_zero (yIter_mem A η s0 t) w.y_mem
  have hkkt := deltaY_kkt A hη s0 t
  have hxnext : xIter A η s0 (t + 1) =
      w.xStar + (xIter A η s0 t - w.xStar) + deltaX A η s0 t := by
    simp only [deltaX]
    abel
  have hu : inner ℝ b (uField A η s0 t) =
      -slackMassY w η s0 t +
        payoff A (xIter A η s0 t - w.xStar) b +
        payoff A (deltaX A η s0 t) b := by
    calc
      inner ℝ b (uField A η s0 t) =
          payoff A (xIter A η s0 (t + 1)) b := by
        rw [payoff]
        simp only [uField]
        rw [real_inner_comm]
      _ = payoff A (w.xStar + (xIter A η s0 t - w.xStar) +
          deltaX A η s0 t) b := by rw [hxnext]
      _ = payoff A w.xStar b +
          payoff A (xIter A η s0 t - w.xStar) b +
          payoff A (deltaX A η s0 t) b := by
        rw [payoff_add_left, payoff_add_left]
      _ = -slackMassY w η s0 t +
          payoff A (xIter A η s0 t - w.xStar) b +
          payoff A (deltaX A η s0 t) b := by
        rw [payoff_witness_left_sub]
  change inner ℝ b (deltaY A η s0 t) =
    -η * slackMassY w η s0 t +
      η * payoff A (xIter A η s0 t - w.xStar) b +
      η * payoff A (deltaX A η s0 t) b +
      η * inner ℝ (rhoKKT A η s0 t) b
  rw [hkkt]
  simp only [real_inner_smul_right, inner_add_right, inner_sub_right,
    real_inner_smul_right]
  rw [hsum, mul_zero, sub_zero, hu,
    real_inner_comm (x := b) (y := rhoKKT A η s0 t)]
  ring

private theorem slackMass_succ (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    slackMass w η s0 (t + 1) = slackMass w η s0 t +
      payoff A (deltaX A η s0 t) w.yStar -
        payoff A w.xStar (deltaY A η s0 t) := by
  have hx : xIter A η s0 (t + 1) =
      xIter A η s0 t + deltaX A η s0 t := by
    simp only [deltaX]
    abel
  have hy : yIter A η s0 (t + 1) =
      yIter A η s0 t + deltaY A η s0 t := by
    simp only [deltaY]
    abel
  have hsx : inner ℝ w.slackX (deltaX A η s0 t) =
      payoff A (deltaX A η s0 t) w.yStar := by
    rw [payoff_eq_inner_adjoint, w.adjoint_eq_value_ones_add_slackX]
    simp only [inner_add_right, real_inner_smul_right]
    have hsum : inner ℝ (deltaX A η s0 t) (ones ι) = 0 := by
      rw [real_inner_comm]
      exact inner_ones_sub_simplex_eq_zero
        (xIter_mem A η s0 (t + 1)) (xIter_mem A η s0 t)
    rw [hsum, mul_zero, zero_add, real_inner_comm]
  have hsy : inner ℝ w.slackY (deltaY A η s0 t) =
      -payoff A w.xStar (deltaY A η s0 t) := by
    rw [payoff, w.map_eq_value_ones_sub_slackY]
    simp only [inner_sub_left, real_inner_smul_left]
    have hsum : inner ℝ (ones κ) (deltaY A η s0 t) = 0 :=
      inner_ones_sub_simplex_eq_zero
        (yIter_mem A η s0 (t + 1)) (yIter_mem A η s0 t)
    rw [hsum, mul_zero, zero_sub]
    ring
  simp only [slackMass, slackMassX, slackMassY, hx, hy, inner_add_right]
  rw [hsx, hsy]
  ring

private theorem energy_difference_expansion (w : GTWitness A) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    energy w η s0 (t + 1) - energy w η s0 t =
      2 * inner ℝ (xIter A η s0 t - w.xStar) (deltaX A η s0 t) +
      ‖deltaX A η s0 t‖ ^ 2 +
      2 * inner ℝ (yIter A η s0 t - w.yStar) (deltaY A η s0 t) +
      ‖deltaY A η s0 t‖ ^ 2 -
      η * (payoff A (deltaX A η s0 t)
          (yIter A η s0 t - w.yStar) +
        payoff A (xIter A η s0 t - w.xStar) (deltaY A η s0 t) +
        payoff A (deltaX A η s0 t) (deltaY A η s0 t)) := by
  have hx : xIter A η s0 (t + 1) - w.xStar =
      (xIter A η s0 t - w.xStar) + deltaX A η s0 t := by
    simp only [deltaX]
    abel
  have hy : yIter A η s0 (t + 1) - w.yStar =
      (yIter A η s0 t - w.yStar) + deltaY A η s0 t := by
    simp only [deltaY]
    abel
  rw [energy, energy, hx, hy, norm_add_sq_real, norm_add_sq_real,
    payoff_add_left, payoff_add_right, payoff_add_right]
  ring

                                                                  
theorem energy_balance (w : GTWitness A) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    energy w η s0 (t + 1) - energy w η s0 t +
        dissipation w η s0 t = residual A η s0 t := by
  have hexpand := energy_difference_expansion w η s0 t
  have hap := energy_inner_x w hη s0 t
  have hbh := energy_inner_y w hη s0 t
  have hP := slackMass_succ w η s0 t
  have hr := residual_eq_eta_mul_pairings A hη s0 t
  have hmu : inner ℝ (muKKT A η s0 t)
      (xIter A η s0 t - w.xStar) =
      inner ℝ (muKKT A η s0 t) (xIter A η s0 t) -
        equilibriumMultiplierX w η s0 t := by
    simp only [inner_sub_right, equilibriumMultiplierX]
  have hrho : inner ℝ (rhoKKT A η s0 t)
      (yIter A η s0 t - w.yStar) =
      inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t) -
        equilibriumMultiplierY w η s0 t := by
    simp only [inner_sub_right, equilibriumMultiplierY]
  have hpayY : payoff A (deltaX A η s0 t) (yIter A η s0 t) =
      payoff A (deltaX A η s0 t) (yIter A η s0 t - w.yStar) +
        payoff A (deltaX A η s0 t) w.yStar := by
    rw [payoff_sub_right]
    ring
  have hpayX : payoff A (xIter A η s0 (t + 1)) (deltaY A η s0 t) =
      payoff A w.xStar (deltaY A η s0 t) +
        payoff A (xIter A η s0 t - w.xStar) (deltaY A η s0 t) +
        payoff A (deltaX A η s0 t) (deltaY A η s0 t) := by
    rw [show xIter A η s0 (t + 1) =
      w.xStar + (xIter A η s0 t - w.xStar) + deltaX A η s0 t by
        simp only [deltaX]
        abel]
    rw [payoff_add_left, payoff_add_left]
  have hres := residual_eq_payoff_movements A η s0 t
  have hcollision : η *
      (inner ℝ (muKKT A η s0 t) (xIter A η s0 t) +
        inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t)) =
      -η * payoff A (deltaX A η s0 t) (yIter A η s0 t) +
        η * payoff A (xIter A η s0 (t + 1)) (deltaY A η s0 t) -
        ‖deltaX A η s0 t‖ ^ 2 - ‖deltaY A η s0 t‖ ^ 2 := by
    rw [← hr]
    exact hres
  rw [hexpand, hap, hbh]
  simp only [dissipation]
  rw [hP, hr, hmu, hrho]
  simp only [equilibriumMultiplier, slackMass]
  rw [hpayY, hpayX] at hcollision
  ring_nf at hcollision ⊢
  linarith

                                           
def movementScale (η L : ℝ) : ℝ := η * L

                                                                    
theorem movementScale_le_inv_two_sqrt_two (w : GTWitness A) {η L : ℝ}
    (hL : 0 < L) (_hη : 0 ≤ η)
    (hstep : η ≤ w.separationDelta L / (2 * Real.sqrt 2 * L)) :
    movementScale η L ≤ 1 / (2 * Real.sqrt 2) := by
  have hsqrt : 0 < 2 * Real.sqrt 2 := by positivity
  have hδ := w.separationDelta_le_one L
  unfold movementScale
  calc
    η * L ≤ (w.separationDelta L / (2 * Real.sqrt 2 * L)) * L :=
      mul_le_mul_of_nonneg_right hstep hL.le
    _ = w.separationDelta L / (2 * Real.sqrt 2) := by
      field_simp [hL.ne']
    _ ≤ 1 / (2 * Real.sqrt 2) :=
      (div_le_div_iff_of_pos_right hsqrt).2 hδ

                                                                        
theorem energy_lower (w : GTWitness A) {η L : ℝ}
    (hη : 0 ≤ η) (hA : ‖A‖ ≤ L)
    (s0 : GameState ι κ) (t : ℕ) :
    (1 - movementScale η L / 2) *
        (‖xIter A η s0 t - w.xStar‖ ^ 2 +
          ‖yIter A η s0 t - w.yStar‖ ^ 2) ≤
      energy w η s0 t := by
  let a := xIter A η s0 t - w.xStar
  let b := yIter A η s0 t - w.yStar
  have hL : 0 ≤ L := (norm_nonneg A).trans hA
  have habs : |payoff A a b| ≤ L * ‖a‖ * ‖b‖ := by
    exact (abs_inner_map_le A a b).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA (norm_nonneg a)) (norm_nonneg b))
  have hpay : payoff A a b ≤ L * ‖a‖ * ‖b‖ :=
    (le_abs_self _).trans habs
  have hpayη : η * payoff A a b ≤ η * (L * ‖a‖ * ‖b‖) :=
    mul_le_mul_of_nonneg_left hpay hη
  have hquad : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hscaled := mul_le_mul_of_nonneg_left hquad (mul_nonneg hη hL)
  change (1 - η * L / 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
    ‖a‖ ^ 2 + ‖b‖ ^ 2 - η * payoff A a b
  nlinarith

                                                                    
theorem energy_nonneg_of_movementScale_le_two (w : GTWitness A) {η L : ℝ}
    (hη : 0 ≤ η) (hA : ‖A‖ ≤ L) (hq : movementScale η L ≤ 2)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ energy w η s0 t := by
  have hlower := energy_lower w hη hA s0 t
  have hcoef : 0 ≤ 1 - movementScale η L / 2 := by linarith
  exact hlower.trans' (mul_nonneg hcoef
    (add_nonneg (sq_nonneg _) (sq_nonneg _)))

                                          
theorem energy_initial_le (w : GTWitness A) {η L : ℝ}
    (hη : 0 ≤ η) (hA : ‖A‖ ≤ L) (s0 : GameState ι κ) :
    energy w η s0 0 ≤ 4 + 2 * movementScale η L := by
  let a := xIter A η s0 0 - w.xStar
  let b := yIter A η s0 0 - w.yStar
  have hL : 0 ≤ L := (norm_nonneg A).trans hA
  have ha2 : ‖a‖ ^ 2 ≤ 2 :=
    simplex_sub_norm_sq_le_two (xIter_mem A η s0 0) w.x_mem
  have hb2 : ‖b‖ ^ 2 ≤ 2 :=
    simplex_sub_norm_sq_le_two (yIter_mem A η s0 0) w.y_mem
  have hab : ‖a‖ * ‖b‖ ≤ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have habs : |payoff A a b| ≤ L * ‖a‖ * ‖b‖ := by
    exact (abs_inner_map_le A a b).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA (norm_nonneg a)) (norm_nonneg b))
  have hpay : -payoff A a b ≤ 2 * L := by
    calc
      -payoff A a b ≤ |payoff A a b| := neg_le_abs _
      _ ≤ L * ‖a‖ * ‖b‖ := habs
      _ ≤ 2 * L := by nlinarith
  have hpayη := mul_le_mul_of_nonneg_left hpay hη
  change ‖a‖ ^ 2 + ‖b‖ ^ 2 - η * payoff A a b ≤ 4 + 2 * (η * L)
  nlinarith

end

end AltGDA
