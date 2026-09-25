import AltGDA.Dynamics.KKTData
import AltGDA.Game.Basic

   
                     

                                                                            
                                                                             
                              
  

open scoped BigOperators RealInnerProductSpace InnerProduct

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                    
def residual (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  η * inner ℝ (vField A η s0 t) (deltaX A η s0 t) +
    η * inner ℝ (uField A η s0 t) (deltaY A η s0 t) -
      ‖deltaX A η s0 t‖ ^ 2 - ‖deltaY A η s0 t‖ ^ 2

                                                             
theorem residual_eq_payoff_movements (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    residual A η s0 t =
      -η * payoff A (deltaX A η s0 t) (yIter A η s0 t) +
        η * payoff A (xIter A η s0 (t + 1)) (deltaY A η s0 t) -
        ‖deltaX A η s0 t‖ ^ 2 - ‖deltaY A η s0 t‖ ^ 2 := by
  have hv : inner ℝ (vField A η s0 t) (deltaX A η s0 t) =
      -payoff A (deltaX A η s0 t) (yIter A η s0 t) := by
    rw [payoff_eq_inner_adjoint]
    simp only [vField, inner_neg_left]
    rw [real_inner_comm]
  have hu : inner ℝ (uField A η s0 t) (deltaY A η s0 t) =
      payoff A (xIter A η s0 (t + 1)) (deltaY A η s0 t) := by
    rfl
  rw [residual, hv, hu]
  ring

private theorem inner_ones_sub_eq_zero {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {x z : EVec α} (hx : x ∈ simplex α) (hz : z ∈ simplex α) :
    inner ℝ (ones α) (x - z) = 0 := by
  rw [PiLp.inner_apply]
  simp only [ones_apply, RCLike.inner_apply, conj_trivial, mul_one,
    PiLp.sub_apply, Finset.sum_sub_distrib, sum_eq_one_of_mem_simplex hx,
    sum_eq_one_of_mem_simplex hz, sub_self]

private theorem inner_multiplier_next_eq_zero {α : Type*}
    [Fintype α] [DecidableEq α]
    (mu xNext : EVec α) (hcomp : ∀ i, mu i * xNext i = 0) :
    inner ℝ mu xNext = 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_eq_zero fun i _ ↦ by simpa [mul_comm] using hcomp i

private theorem projection_block_residual_eq {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {x xNext v mu : EVec α} {η gamma : ℝ}
    (hx : x ∈ simplex α) (hxNext : xNext ∈ simplex α)
    (hstep : xNext - x = η • (v - gamma • ones α + mu))
    (hcomp : ∀ i, mu i * xNext i = 0) :
    η * inner ℝ v (xNext - x) - ‖xNext - x‖ ^ 2 =
      η * inner ℝ mu x := by
  let d : EVec α := xNext - x
  have hsum : inner ℝ (ones α) d = 0 := by
    simpa [d] using inner_ones_sub_eq_zero hxNext hx
  have hmuNext : inner ℝ mu xNext = 0 :=
    inner_multiplier_next_eq_zero mu xNext hcomp
  have hmuD : inner ℝ mu d = -inner ℝ mu x := by
    simp only [d, inner_sub_right, hmuNext, zero_sub]
  have hnorm : ‖d‖ ^ 2 =
      η * (inner ℝ v d + inner ℝ mu d) := by
    calc
      ‖d‖ ^ 2 = inner ℝ d d := (real_inner_self_eq_norm_sq d).symm
      _ = inner ℝ (η • (v - gamma • ones α + mu)) d := by
        rw [← hstep]
      _ = η * (inner ℝ v d + inner ℝ mu d) := by
        simp only [real_inner_smul_left, inner_add_left, inner_sub_left]
        rw [hsum]
        ring
  change η * inner ℝ v d - ‖d‖ ^ 2 = η * inner ℝ mu x
  rw [hnorm, hmuD]
  ring

                                                                              
theorem xResidualBlock_eq (A : PayoffOperator ι κ) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    η * inner ℝ (vField A η s0 t) (deltaX A η s0 t) -
        ‖deltaX A η s0 t‖ ^ 2 =
      η * inner ℝ (muKKT A η s0 t) (xIter A η s0 t) := by
  exact projection_block_residual_eq
    (xIter_mem A η s0 t) (xIter_mem A η s0 (t + 1))
    (deltaX_kkt A hη s0 t) (muKKT_complementarity A η s0 t)

                                                                               
theorem yResidualBlock_eq (A : PayoffOperator ι κ) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    η * inner ℝ (uField A η s0 t) (deltaY A η s0 t) -
        ‖deltaY A η s0 t‖ ^ 2 =
      η * inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t) := by
  exact projection_block_residual_eq
    (yIter_mem A η s0 t) (yIter_mem A η s0 (t + 1))
    (deltaY_kkt A hη s0 t) (rhoKKT_complementarity A η s0 t)

                                                     
theorem residual_eq_eta_mul_pairings (A : PayoffOperator ι κ) {η : ℝ}
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    residual A η s0 t = η *
      (inner ℝ (muKKT A η s0 t) (xIter A η s0 t) +
        inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t)) := by
  rw [residual]
  have hx := xResidualBlock_eq A hη s0 t
  have hy := yResidualBlock_eq A hη s0 t
  linarith

theorem muKKT_inner_xIter_nonneg (A : PayoffOperator ι κ) {η : ℝ}
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ inner ℝ (muKKT A η s0 t) (xIter A η s0 t) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_nonneg
  intro i _
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_nonneg (nonneg_of_mem_simplex (xIter_mem A η s0 t) i)
    (muKKT_nonneg A hη s0 t i)

theorem rhoKKT_inner_yIter_nonneg (A : PayoffOperator ι κ) {η : ℝ}
    (hη : 0 < η) (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ inner ℝ (rhoKKT A η s0 t) (yIter A η s0 t) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_nonneg
  intro j _
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_nonneg (nonneg_of_mem_simplex (yIter_mem A η s0 t) j)
    (rhoKKT_nonneg A hη s0 t j)

                                             
theorem residual_nonneg (A : PayoffOperator ι κ) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    0 ≤ residual A η s0 t := by
  rw [residual_eq_eta_mul_pairings A hη s0 t]
  exact mul_nonneg hη.le
    (add_nonneg (muKKT_inner_xIter_nonneg A hη s0 t)
      (rhoKKT_inner_yIter_nonneg A hη s0 t))

end

end AltGDA
