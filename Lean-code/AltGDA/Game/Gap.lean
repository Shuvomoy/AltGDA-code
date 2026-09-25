import AltGDA.Game.Basic

   
                                                    

                                                                           
                                                                            
                                                                             
                                                                           
                      
  

open scoped BigOperators InnerProduct

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                               
def upperValue (A : PayoffOperator ι κ) (x : EVec ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j ↦ (A x) j

                                                               
def lowerValue (A : PayoffOperator ι κ) (y : EVec κ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i ↦ (payoffAdjoint A y) i

                                                                      
def dualityGap (A : PayoffOperator ι κ) (x : EVec ι) (y : EVec κ) : ℝ :=
  upperValue A x - lowerValue A y

theorem le_upperValue (A : PayoffOperator ι κ) (x : EVec ι) (j : κ) :
    (A x) j ≤ upperValue A x := by
  simpa only [upperValue] using
    (Finset.le_sup' (s := Finset.univ) (f := fun k ↦ (A x) k) (Finset.mem_univ j))

theorem lowerValue_le (A : PayoffOperator ι κ) (y : EVec κ) (i : ι) :
    lowerValue A y ≤ (payoffAdjoint A y) i := by
  simpa only [lowerValue] using
    (Finset.inf'_le (s := Finset.univ) (f := fun k ↦ (payoffAdjoint A y) k)
      (Finset.mem_univ i))

theorem upperValue_le_iff (A : PayoffOperator ι κ) (x : EVec ι) {a : ℝ} :
    upperValue A x ≤ a ↔ ∀ j, (A x) j ≤ a := by
  simp [upperValue, Finset.sup'_le_iff]

theorem le_lowerValue_iff (A : PayoffOperator ι κ) (y : EVec κ) {a : ℝ} :
    a ≤ lowerValue A y ↔ ∀ i, a ≤ (payoffAdjoint A y) i := by
  simp [lowerValue, Finset.le_inf'_iff]

theorem exists_upperValue_coordinate (A : PayoffOperator ι κ) (x : EVec ι) :
    ∃ j : κ, upperValue A x = (A x) j := by
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k : κ ↦ (A x) k)
  exact ⟨j, hj⟩

theorem exists_lowerValue_coordinate (A : PayoffOperator ι κ) (y : EVec κ) :
    ∃ i : ι, lowerValue A y = (payoffAdjoint A y) i := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun k : ι ↦ (payoffAdjoint A y) k)
  exact ⟨i, hi⟩

@[simp]
theorem payoff_simplexVertex_right (A : PayoffOperator ι κ)
    (x : EVec ι) (j : κ) :
    payoff A x (simplexVertex j) = (A x) j := by
  rw [payoff_eq_sum]
  classical
  simp [simplexVertex_apply]

@[simp]
theorem payoff_simplexVertex_left (A : PayoffOperator ι κ)
    (i : ι) (y : EVec κ) :
    payoff A (simplexVertex i) y = (payoffAdjoint A y) i := by
  rw [payoff_eq_inner_adjoint]
  simp [simplexVertex, EuclideanSpace.inner_single_left]

                                                                                 
theorem payoff_le_upperValue (A : PayoffOperator ι κ)
    (x : EVec ι) {y : EVec κ} (hy : y ∈ simplex κ) :
    payoff A x y ≤ upperValue A x := by
  rw [payoff_eq_sum]
  calc
    (∑ j, (A x) j * y j) ≤ ∑ j, upperValue A x * y j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (le_upperValue A x j) (simplex_nonneg hy j)
    _ = upperValue A x * ∑ j, y j := by rw [Finset.mul_sum]
    _ = upperValue A x := by rw [simplex_sum hy, mul_one]

                                                                                       
theorem lowerValue_le_payoff (A : PayoffOperator ι κ)
    {x : EVec ι} (hx : x ∈ simplex ι) (y : EVec κ) :
    lowerValue A y ≤ payoff A x y := by
  rw [payoff_eq_inner_adjoint]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc
    lowerValue A y = (∑ i, x i) * lowerValue A y := by rw [simplex_sum hx, one_mul]
    _ = ∑ i, x i * lowerValue A y := by rw [Finset.sum_mul]
    _ ≤ ∑ i, x i * (payoffAdjoint A y) i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (lowerValue_le A y i) (simplex_nonneg hx i)
    _ = ∑ i, (payoffAdjoint A y) i * x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]

                                                                 
theorem exists_simplex_payoff_eq_upperValue (A : PayoffOperator ι κ) (x : EVec ι) :
    ∃ y ∈ simplex κ, payoff A x y = upperValue A x := by
  obtain ⟨j, hj⟩ := exists_upperValue_coordinate A x
  exact ⟨simplexVertex j, simplexVertex_mem j, by simp [hj]⟩

                                                                 
theorem exists_simplex_payoff_eq_lowerValue (A : PayoffOperator ι κ) (y : EVec κ) :
    ∃ x ∈ simplex ι, payoff A x y = lowerValue A y := by
  obtain ⟨i, hi⟩ := exists_lowerValue_coordinate A y
  exact ⟨simplexVertex i, simplexVertex_mem i, by simp [hi]⟩

                                                             
theorem upperValue_isGreatest (A : PayoffOperator ι κ) (x : EVec ι) :
    IsGreatest ((fun y : EVec κ ↦ payoff A x y) '' simplex κ) (upperValue A x) := by
  constructor
  · obtain ⟨y, hy, hpay⟩ := exists_simplex_payoff_eq_upperValue A x
    exact ⟨y, hy, hpay⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact payoff_le_upperValue A x hy

                                                             
theorem lowerValue_isLeast (A : PayoffOperator ι κ) (y : EVec κ) :
    IsLeast ((fun x : EVec ι ↦ payoff A x y) '' simplex ι) (lowerValue A y) := by
  constructor
  · obtain ⟨x, hx, hpay⟩ := exists_simplex_payoff_eq_lowerValue A y
    exact ⟨x, hx, hpay⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact lowerValue_le_payoff A hx y

theorem IsSaddle.upperValue_eq_payoff {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsSaddle A x y) :
    upperValue A x = payoff A x y := by
  obtain ⟨yHat, hyHat, hupper⟩ := exists_simplex_payoff_eq_upperValue A x
  apply le_antisymm
  · calc
      upperValue A x = payoff A x yHat := hupper.symm
      _ ≤ payoff A x y := h.max_inequality hyHat
  · exact payoff_le_upperValue A x h.y_mem

theorem IsSaddle.lowerValue_eq_payoff {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsSaddle A x y) :
    lowerValue A y = payoff A x y := by
  obtain ⟨xHat, hxHat, hlower⟩ := exists_simplex_payoff_eq_lowerValue A y
  apply le_antisymm
  · exact lowerValue_le_payoff A h.x_mem y
  · calc
      payoff A x y ≤ payoff A xHat y := h.min_inequality hxHat
      _ = lowerValue A y := hlower

                                                                                      
theorem exists_comparators_dualityGap_eq (A : PayoffOperator ι κ)
    (x : EVec ι) (y : EVec κ) :
    ∃ xHat ∈ simplex ι, ∃ yHat ∈ simplex κ,
      dualityGap A x y = payoff A x yHat - payoff A xHat y := by
  obtain ⟨xHat, hxHat, hmin⟩ := exists_simplex_payoff_eq_lowerValue A y
  obtain ⟨yHat, hyHat, hmax⟩ := exists_simplex_payoff_eq_upperValue A x
  exact ⟨xHat, hxHat, yHat, hyHat, by simp [dualityGap, hmax, hmin]⟩

                                                                         
theorem dualityGap_nonneg (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    0 ≤ dualityGap A x y := by
  have hlo := lowerValue_le_payoff A hx y
  have hup := payoff_le_upperValue A x hy
  unfold dualityGap
  linarith

                                                                                       
theorem abs_payoff_le_opNorm (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    |payoff A x y| ≤ ‖A‖ := by
  calc
    |payoff A x y| ≤ ‖A‖ * ‖x‖ * ‖y‖ := abs_inner_map_le A x y
    _ ≤ ‖A‖ * 1 * 1 := by
      gcongr
      · exact simplex_norm_le_one hx
      · exact simplex_norm_le_one hy
    _ = ‖A‖ := by ring

theorem upperValue_le_opNorm (A : PayoffOperator ι κ)
    {x : EVec ι} (hx : x ∈ simplex ι) :
    upperValue A x ≤ ‖A‖ := by
  obtain ⟨yHat, hyHat, hupper⟩ := exists_simplex_payoff_eq_upperValue A x
  rw [← hupper]
  exact (le_abs_self (payoff A x yHat)).trans (abs_payoff_le_opNorm A hx hyHat)

theorem neg_opNorm_le_lowerValue (A : PayoffOperator ι κ)
    {y : EVec κ} (hy : y ∈ simplex κ) :
    -‖A‖ ≤ lowerValue A y := by
  obtain ⟨xHat, hxHat, hlower⟩ := exists_simplex_payoff_eq_lowerValue A y
  rw [← hlower]
  exact neg_le_of_abs_le (abs_payoff_le_opNorm A hxHat hy)

                                                                          
theorem dualityGap_le_two_opNorm (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    dualityGap A x y ≤ 2 * ‖A‖ := by
  have hu := upperValue_le_opNorm A hx
  have hl := neg_opNorm_le_lowerValue A hy
  unfold dualityGap
  linarith

                                                                               
theorem isSaddle_iff_dualityGap_eq_zero (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    IsSaddle A x y ↔ dualityGap A x y = 0 := by
  constructor
  · intro hs
    rw [dualityGap, hs.upperValue_eq_payoff, hs.lowerValue_eq_payoff, sub_self]
  · intro hgap
    have heq : upperValue A x = lowerValue A y := by
      unfold dualityGap at hgap
      linarith
    refine ⟨hx, hy, ?_, ?_⟩
    · intro y' hy'
      calc
        payoff A x y' ≤ upperValue A x := payoff_le_upperValue A x hy'
        _ = lowerValue A y := heq
        _ ≤ payoff A x y := lowerValue_le_payoff A hx y
    · intro x' hx'
      calc
        payoff A x y ≤ upperValue A x := payoff_le_upperValue A x hy
        _ = lowerValue A y := heq
        _ ≤ payoff A x' y := lowerValue_le_payoff A hx' y

theorem IsSaddle.dualityGap_eq_zero {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsSaddle A x y) :
    dualityGap A x y = 0 :=
  (isSaddle_iff_dualityGap_eq_zero A h.x_mem h.y_mem).mp h

end

end AltGDA
