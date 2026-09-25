import AltGDA.Analysis.ShiftedTelescope
import AltGDA.Analysis.Residual
import AltGDA.Dynamics.KKTData
import AltGDA.Game.Gap

   
                                                    

                                                                    
                                                                           
                                                                        
  

open scoped BigOperators RealInnerProductSpace InnerProduct

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                   
theorem simplex_projection_update_inequality
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p g z : EVec α) (η : ℝ) (hz : z ∈ simplex α) :
    η * ⟪g, z - simplexProj (p + η • g)⟫ ≤
      (1 / 2 : ℝ) *
        (‖p - z‖ ^ 2 - ‖simplexProj (p + η • g) - z‖ ^ 2 -
          ‖simplexProj (p + η • g) - p‖ ^ 2) := by
  have hvi := simplexProj_variational_inequality (p + η • g) hz
  have hinner :
      η * ⟪g, z - simplexProj (p + η • g)⟫ ≤
        ⟪simplexProj (p + η • g) - p,
          z - simplexProj (p + η • g)⟫ := by
    simp only [inner_add_left, inner_sub_left, inner_smul_left,
      RCLike.conj_to_real] at hvi
    simp only [inner_sub_left]
    linarith
  calc
    η * ⟪g, z - simplexProj (p + η • g)⟫ ≤
        ⟪simplexProj (p + η • g) - p,
          z - simplexProj (p + η • g)⟫ := hinner
    _ = (1 / 2 : ℝ) *
        (‖p - z‖ ^ 2 - ‖simplexProj (p + η • g) - z‖ ^ 2 -
          ‖simplexProj (p + η • g) - p‖ ^ 2) := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring

                                                
def comparatorGap (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (x : EVec ι) (y : EVec κ) (t : ℕ) : ℝ :=
  payoff A (xIter A η s0 t) y - payoff A x (yIter A η s0 t)

                                                    
def phiPotential (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (x : EVec ι) (y : EVec κ) (t : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ‖xIter A η s0 t - x‖ ^ 2 +
  (1 / 2 : ℝ) * ‖yIter A η s0 t - y‖ ^ 2 +
  η * payoff A x (yIter A η s0 t)

                                                     
def psiPotential (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (x : EVec ι) (y : EVec κ) (t : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ‖xIter A η s0 t - x‖ ^ 2 +
  (1 / 2 : ℝ) * ‖yIter A η s0 (t - 1) - y‖ ^ 2 -
  (1 / 2 : ℝ) * ‖yIter A η s0 t - yIter A η s0 (t - 1)‖ ^ 2

def shiftedPotential (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (x : EVec ι) (y : EVec κ) (t : ℕ) : ℝ :=
  phiPotential A η s0 x y t + psiPotential A η s0 x y t

theorem inner_vField_comparator (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) (x : EVec ι) :
    ⟪vField A η s0 t, x - xIter A η s0 (t + 1)⟫ =
      payoff A (xIter A η s0 (t + 1)) (yIter A η s0 t) -
        payoff A x (yIter A η s0 t) := by
  simp only [vField, payoff, inner_neg_left]
  rw [real_inner_comm]
  rw [← inner_map_eq_inner_adjoint]
  rw [map_sub, inner_sub_left]
  ring

theorem inner_uField_comparator (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) (y : EVec κ) :
    ⟪uField A η s0 t, y - yIter A η s0 (t + 1)⟫ =
      payoff A (xIter A η s0 (t + 1)) y -
        payoff A (xIter A η s0 (t + 1)) (yIter A η s0 (t + 1)) := by
  simp [uField, payoff, inner_sub_right]

theorem inner_uField_deltaY (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    ⟪uField A η s0 t, deltaY A η s0 t⟫ =
      payoff A (xIter A η s0 (t + 1)) (yIter A η s0 (t + 1)) -
        payoff A (xIter A η s0 (t + 1)) (yIter A η s0 t) := by
  simp [uField, deltaY, payoff, inner_sub_right]

theorem inner_vField_deltaX (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    ⟪vField A η s0 t, deltaX A η s0 t⟫ =
      payoff A (xIter A η s0 t) (yIter A η s0 t) -
        payoff A (xIter A η s0 (t + 1)) (yIter A η s0 t) := by
  simp only [vField, deltaX, payoff, inner_neg_left]
  rw [real_inner_comm]
  rw [← inner_map_eq_inner_adjoint]
  rw [map_sub, inner_sub_left]
  ring

                                                                 
theorem shifted_projection_one (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) {x : EVec ι} {y : EVec κ}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) (t : ℕ) :
    η * comparatorGap A η s0 x y (t + 1) ≤
      phiPotential A η s0 x y t - phiPotential A η s0 x y (t + 1) +
      η * ⟪uField A η s0 t, deltaY A η s0 t⟫ -
      (1 / 2 : ℝ) *
        (‖deltaX A η s0 t‖ ^ 2 + ‖deltaY A η s0 t‖ ^ 2) := by
  have hxvi := simplex_projection_update_inequality
    (xIter A η s0 t) (vField A η s0 t) x η hx
  have hyvi := simplex_projection_update_inequality
    (yIter A η s0 t) (uField A η s0 t) y η hy
  rw [← xIter_succ_eq_projection] at hxvi
  rw [← yIter_succ_eq_projection] at hyvi
  rw [inner_vField_comparator] at hxvi
  rw [inner_uField_comparator] at hyvi
  rw [inner_uField_deltaY]
  simp only [deltaX, deltaY, comparatorGap, phiPotential]
  nlinarith [hxvi, hyvi]

                                                                  
theorem shifted_projection_two (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) {x : EVec ι} {y : EVec κ}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex κ)
    (t : ℕ) (ht : 1 ≤ t) :
    η * comparatorGap A η s0 x y t ≤
      psiPotential A η s0 x y t - psiPotential A η s0 x y (t + 1) +
      η * ⟪vField A η s0 t, deltaX A η s0 t⟫ -
      (1 / 2 : ℝ) *
        (‖deltaX A η s0 t‖ ^ 2 + ‖deltaY A η s0 t‖ ^ 2) := by
  let k := t - 1
  have hkt : k + 1 = t := by
    dsimp [k]
    omega
  have hxvi := simplex_projection_update_inequality
    (xIter A η s0 t) (vField A η s0 t) x η hx
  have hyvi := simplex_projection_update_inequality
    (yIter A η s0 k) (uField A η s0 k) y η hy
  rw [← xIter_succ_eq_projection] at hxvi
  rw [← yIter_succ_eq_projection] at hyvi
  rw [hkt] at hyvi
  rw [inner_vField_comparator] at hxvi
  have hyrewrite := inner_uField_comparator A η s0 k y
  rw [hkt] at hyrewrite
  rw [hyrewrite] at hyvi
  rw [inner_vField_deltaX]
  simp only [deltaX, deltaY, comparatorGap, psiPotential,
    Nat.add_sub_cancel]
  change _ ≤
    (1 / 2 : ℝ) * ‖xIter A η s0 t - x‖ ^ 2 +
      (1 / 2 : ℝ) * ‖yIter A η s0 k - y‖ ^ 2 -
      (1 / 2 : ℝ) * ‖yIter A η s0 t - yIter A η s0 k‖ ^ 2 -
      ((1 / 2 : ℝ) * ‖xIter A η s0 (t + 1) - x‖ ^ 2 +
        (1 / 2 : ℝ) * ‖yIter A η s0 t - y‖ ^ 2 -
        (1 / 2 : ℝ) * ‖yIter A η s0 (t + 1) - yIter A η s0 t‖ ^ 2) +
      η *
        (payoff A (xIter A η s0 t) (yIter A η s0 t) -
          payoff A (xIter A η s0 (t + 1)) (yIter A η s0 t)) -
      (1 / 2 : ℝ) *
        (‖xIter A η s0 (t + 1) - xIter A η s0 t‖ ^ 2 +
          ‖yIter A η s0 (t + 1) - yIter A η s0 t‖ ^ 2)
  nlinarith [hxvi, hyvi]

                                                                      
theorem combined_shifted_projection (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) {x : EVec ι} {y : EVec κ}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex κ)
    (t : ℕ) (ht : 1 ≤ t) :
    η * (comparatorGap A η s0 x y t +
      comparatorGap A η s0 x y (t + 1)) ≤
      shiftedPotential A η s0 x y t -
        shiftedPotential A η s0 x y (t + 1) + residual A η s0 t := by
  have h1 := shifted_projection_one A η s0 hx hy t
  have h2 := shifted_projection_two A η s0 hx hy t ht
  unfold shiftedPotential residual
  nlinarith

theorem payoff_le_of_opNorm_le (A : PayoffOperator ι κ) {L : ℝ}
    (hA : ‖A‖ ≤ L) {x : EVec ι} {y : EVec κ}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    payoff A x y ≤ L := by
  exact (le_abs_self _).trans ((abs_payoff_le_opNorm A hx hy).trans hA)

theorem neg_payoff_le_of_opNorm_le (A : PayoffOperator ι κ) {L : ℝ}
    (hA : ‖A‖ ≤ L) {x : EVec ι} {y : EVec κ}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    -payoff A x y ≤ L := by
  have hneg : -L ≤ payoff A x y :=
    neg_le_of_abs_le ((abs_payoff_le_opNorm A hx hy).trans hA)
  linarith

                                                    
theorem shiftedPotential_one_le (A : PayoffOperator ι κ) {L η : ℝ}
    (hA : ‖A‖ ≤ L) (hη : 0 ≤ η)
    (s0 : GameState ι κ) {x : EVec ι} {y : EVec κ}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    shiftedPotential A η s0 x y 1 ≤ 4 + η * L := by
  have hxx := simplex_sub_norm_sq_le_two (xIter_mem A η s0 1) hx
  have hyy := simplex_sub_norm_sq_le_two (yIter_mem A η s0 1) hy
  have hy0 := simplex_sub_norm_sq_le_two (yIter_mem A η s0 0) hy
  have hpay := payoff_le_of_opNorm_le A hA hx (yIter_mem A η s0 1)
  have hpayη : η * payoff A x (yIter A η s0 1) ≤ η * L :=
    mul_le_mul_of_nonneg_left hpay hη
  have hmove : 0 ≤ ‖yIter A η s0 1 - yIter A η s0 0‖ ^ 2 := sq_nonneg _
  simp [shiftedPotential, phiPotential, psiPotential]
  nlinarith

                                                         
theorem neg_shiftedPotential_le (A : PayoffOperator ι κ) {L η : ℝ}
    (hL : 0 < L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) {x : EVec ι} {y : EVec κ}
    (hx : x ∈ simplex ι) (hy : y ∈ simplex κ)
    (T : ℕ) (hT : 1 ≤ T) :
    -shiftedPotential A η s0 x y T ≤
      η * L + (1 / 2 : ℝ) * (η * L) ^ 2 := by
  let k := T - 1
  have hkt : k + 1 = T := by
    dsimp [k]
    omega
  have hmove := deltaY_norm_le A hL.le hA hη s0 k
  simp only [deltaY] at hmove
  rw [hkt] at hmove
  have hmoveSq :
      ‖yIter A η s0 T - yIter A η s0 k‖ ^ 2 ≤ (η * L) ^ 2 := by
    have hq : 0 ≤ η * L := mul_nonneg hη.le hL.le
    nlinarith [norm_nonneg (yIter A η s0 T - yIter A η s0 k)]
  have hpay := neg_payoff_le_of_opNorm_le A hA hx (yIter_mem A η s0 T)
  have hpayη : -η * payoff A x (yIter A η s0 T) ≤ η * L := by
    nlinarith
  have hxx : 0 ≤ ‖xIter A η s0 T - x‖ ^ 2 := sq_nonneg _
  have hyy : 0 ≤ ‖yIter A η s0 T - y‖ ^ 2 := sq_nonneg _
  have hyprev : 0 ≤ ‖yIter A η s0 k - y‖ ^ 2 := sq_nonneg _
  simp only [shiftedPotential, phiPotential, psiPotential]
  change -((1 / 2 : ℝ) * ‖xIter A η s0 T - x‖ ^ 2 +
      (1 / 2 : ℝ) * ‖yIter A η s0 T - y‖ ^ 2 +
      η * payoff A x (yIter A η s0 T) +
      ((1 / 2 : ℝ) * ‖xIter A η s0 T - x‖ ^ 2 +
        (1 / 2 : ℝ) * ‖yIter A η s0 k - y‖ ^ 2 -
        (1 / 2 : ℝ) * ‖yIter A η s0 T - yIter A η s0 k‖ ^ 2)) ≤ _
  nlinarith

theorem comparatorGap_le_two_mul (A : PayoffOperator ι κ) {L η : ℝ}
    (hA : ‖A‖ ≤ L) (s0 : GameState ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ)
    (t : ℕ) :
    comparatorGap A η s0 x y t ≤ 2 * L := by
  have hupper := payoff_le_of_opNorm_le A hA (xIter_mem A η s0 t) hy
  have hlower := neg_payoff_le_of_opNorm_le A hA hx (yIter_mem A η s0 t)
  unfold comparatorGap
  linarith

                                                                     
theorem comparatorGap_endpoints_le (A : PayoffOperator ι κ) {L η : ℝ}
    (hA : ‖A‖ ≤ L) (hη : 0 ≤ η) (s0 : GameState ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ)
    (T : ℕ) :
    η * (comparatorGap A η s0 x y 1 + comparatorGap A η s0 x y T) ≤
      4 * (η * L) := by
  have h1 := comparatorGap_le_two_mul (η := η) A hA s0 hx hy 1
  have hT := comparatorGap_le_two_mul (η := η) A hA s0 hx hy T
  nlinarith

theorem payoff_finset_sum_left (A : PayoffOperator ι κ)
    {β : Type*} (s : Finset β) (f : β → EVec ι) (y : EVec κ) :
    payoff A (∑ b ∈ s, f b) y = ∑ b ∈ s, payoff A (f b) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih => simp [hb, ih, payoff_add_left]

theorem payoff_finset_sum_right (A : PayoffOperator ι κ)
    {β : Type*} (s : Finset β) (x : EVec ι) (f : β → EVec κ) :
    payoff A x (∑ b ∈ s, f b) = ∑ b ∈ s, payoff A x (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih => simp [hb, ih, payoff_add_right]

theorem payoff_avgX (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (T : ℕ) (y : EVec κ) :
    payoff A (avgX A η s0 T) y =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        payoff A (xIter A η s0 (t + 1)) y := by
  rw [avgX, payoff_smul_left]
  rw [payoff_finset_sum_left]
  rw [Finset.sum_fin_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem payoff_avgY (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (T : ℕ) (x : EVec ι) :
    payoff A x (avgY A η s0 T) =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        payoff A x (yIter A η s0 (t + 1)) := by
  rw [avgY, payoff_smul_right]
  rw [payoff_finset_sum_right]
  rw [Finset.sum_fin_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

                                                                                
theorem sum_comparatorGap_eq_natCast_mul_average
    (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ)
    (T : ℕ) (hT : 0 < T) (x : EVec ι) (y : EVec κ) :
    ∑ t ∈ Finset.range T, comparatorGap A η s0 x y (t + 1) =
      (T : ℝ) *
        (payoff A (avgX A η s0 T) y - payoff A x (avgY A η s0 T)) := by
  rw [payoff_avgX, payoff_avgY]
  simp only [comparatorGap, Finset.sum_sub_distrib]
  have hcast : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  field_simp

   
                                                                        
                                       
  
theorem dualityGap_avg_le_of_comparator_sum
    (A : PayoffOperator ι κ) {η C : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (T : ℕ) (hT : 0 < T)
    (hsum : ∀ x ∈ simplex ι, ∀ y ∈ simplex κ,
      2 * η * (∑ t ∈ Finset.range T,
        comparatorGap A η s0 x y (t + 1)) ≤ C) :
    dualityGap A (avgX A η s0 T) (avgY A η s0 T) ≤
      C / (2 * η * T) := by
  obtain ⟨xHat, hxHat, yHat, hyHat, hgap⟩ :=
    exists_comparators_dualityGap_eq A (avgX A η s0 T) (avgY A η s0 T)
  have hbound := hsum xHat hxHat yHat hyHat
  have havg := sum_comparatorGap_eq_natCast_mul_average
    A η s0 T hT xHat yHat
  rw [havg] at hbound
  have hdenom : 0 < 2 * η * (T : ℝ) := by positivity
  apply (le_div_iff₀ hdenom).2
  rw [hgap]
  nlinarith

end

end AltGDA
