import AltGDA.Game.Gap
import AltGDA.Game.Witness
import Mathlib.Topology.Sion

   
                                               

                                                                     
                                                 
  

open scoped BigOperators InnerProduct RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                               
def payoffLeftCLM (A : PayoffOperator ι κ) (y : EVec κ) : EVec ι →L[ℝ] ℝ :=
  { toFun := fun x ↦ payoff A x y
    map_add' := fun x z ↦ payoff_add_left A x z y
    map_smul' := fun a x ↦ by simp [payoff_smul_left]
    cont := A.continuous.inner continuous_const }

                                                                               
def payoffRightCLM (A : PayoffOperator ι κ) (x : EVec ι) : EVec κ →L[ℝ] ℝ :=
  { toFun := fun y ↦ payoff A x y
    map_add' := payoff_add_right A x
    map_smul' := fun a y ↦ by simp [payoff_smul_right]
    cont := continuous_const.inner continuous_id }

@[simp]
theorem payoffLeftCLM_apply (A : PayoffOperator ι κ) (y : EVec κ) (x : EVec ι) :
    payoffLeftCLM A y x = payoff A x y := by
  rfl

@[simp]
theorem payoffRightCLM_apply (A : PayoffOperator ι κ) (x : EVec ι) (y : EVec κ) :
    payoffRightCLM A x y = payoff A x y := by
  rfl

                                                                     
theorem exists_isSaddle (A : PayoffOperator ι κ) :
    ∃ x : EVec ι, ∃ y : EVec κ, IsSaddle A x y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Sion.exists_isSaddlePointOn
    (X := simplex ι) (Y := simplex κ) (f := payoff A)
    simplex_nonempty simplex_convex simplex_isCompact
    (fun y _ ↦ by
      simpa [payoffLeftCLM, payoff, real_inner_comm] using
        (payoffLeftCLM A y).continuous.lowerSemicontinuous.lowerSemicontinuousOn (simplex ι))
    (fun y _ ↦ by
      simpa [payoffLeftCLM, payoff, real_inner_comm] using
        ((payoffLeftCLM A y).toLinearMap.convexOn simplex_convex).quasiconvexOn)
    simplex_convex simplex_nonempty simplex_isCompact
    (fun x _ ↦ by
      simpa [payoffRightCLM, payoff, real_inner_comm] using
        (payoffRightCLM A x).continuous.upperSemicontinuous.upperSemicontinuousOn (simplex κ))
    (fun x _ ↦ by
      simpa [payoffRightCLM, payoff, real_inner_comm] using
        ((payoffRightCLM A x).toLinearMap.concaveOn simplex_convex).quasiconcaveOn)
  refine ⟨x, y, hx, hy, ?_, ?_⟩
  · intro y' hy'
    exact hxy x hx y' hy'
  · intro x' hx'
    exact hxy x' hx' y hy

                                                                        
theorem IsSaddle.xSlackAt_nonneg {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsSaddle A x y) (i : ι) :
    0 ≤ xSlackAt A y (saddleValue A x y) i := by
  have hi := h.min_inequality (simplexVertex_mem i)
  simpa [saddleValue] using sub_nonneg.mpr hi

                                                                        
theorem IsSaddle.ySlackAt_nonneg {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsSaddle A x y) (j : κ) :
    0 ≤ ySlackAt A x (saddleValue A x y) j := by
  have hj := h.max_inequality (simplexVertex_mem j)
  simpa [saddleValue] using sub_nonneg.mpr hj

                                                                                            
theorem IsSaddle.x_mul_xSlackAt {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsSaddle A x y) (i : ι) :
    x i * xSlackAt A y (saddleValue A x y) i = 0 := by
  have hinner : (∑ k, x k * payoffAdjoint A y k) = payoff A x y := by
    rw [payoff_eq_inner_adjoint]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsum : (∑ k, x k * xSlackAt A y (saddleValue A x y) k) = 0 := by
    simp_rw [xSlackAt_apply, mul_sub]
    rw [Finset.sum_sub_distrib, hinner, ← Finset.sum_mul, simplex_sum h.x_mem]
    simp [saddleValue]
  have hnonneg : ∀ k ∈ (Finset.univ : Finset ι),
      0 ≤ x k * xSlackAt A y (saddleValue A x y) k := by
    intro k _
    exact mul_nonneg (simplex_nonneg h.x_mem k) (h.xSlackAt_nonneg k)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (by simpa using hsum)
  exact hall i (Finset.mem_univ i)

                                                                                            
theorem IsSaddle.y_mul_ySlackAt {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsSaddle A x y) (j : κ) :
    y j * ySlackAt A x (saddleValue A x y) j = 0 := by
  have hpay : (∑ k, y k * A x k) = payoff A x y := by
    rw [payoff_eq_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsum : (∑ k, y k * ySlackAt A x (saddleValue A x y) k) = 0 := by
    simp_rw [ySlackAt_apply, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, simplex_sum h.y_mem, one_mul, hpay]
    simp [saddleValue]
  have hnonneg : ∀ k ∈ (Finset.univ : Finset κ),
      0 ≤ y k * ySlackAt A x (saddleValue A x y) k := by
    intro k _
    exact mul_nonneg (simplex_nonneg h.y_mem k) (h.ySlackAt_nonneg k)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (by simpa using hsum)
  exact hall j (Finset.mem_univ j)

   
                                                                              

                                                                       
                                                                        
                                                                         
                             
  
def IsQuasiStrictSaddle (A : PayoffOperator ι κ) (x : EVec ι) (y : EVec κ) : Prop :=
  IsSaddle A x y ∧
    (∀ i, 0 < x i ∨ 0 < xSlackAt A y (saddleValue A x y) i) ∧
      (∀ j, 0 < y j ∨ 0 < ySlackAt A x (saddleValue A x y) j)

                                                                                        
def gtWitness_of_quasiStrictSaddle {A : PayoffOperator ι κ}
    {x : EVec ι} {y : EVec κ} (h : IsQuasiStrictSaddle A x y) : GTWitness A where
  xStar := x
  yStar := y
  saddle := h.1
  xSlack_nonneg := h.1.xSlackAt_nonneg
  ySlack_nonneg := h.1.ySlackAt_nonneg
  x_complementary := h.1.x_mul_xSlackAt
  y_complementary := h.1.y_mul_ySlackAt
  x_strictComplementary := by
    intro i
    rcases h.2.1 i with hx | hs
    · exact add_pos_of_pos_of_nonneg hx (h.1.xSlackAt_nonneg i)
    · exact add_pos_of_nonneg_of_pos (simplex_nonneg h.1.x_mem i) hs
  y_strictComplementary := by
    intro j
    rcases h.2.2 j with hy | hs
    · exact add_pos_of_pos_of_nonneg hy (h.1.ySlackAt_nonneg j)
    · exact add_pos_of_nonneg_of_pos (simplex_nonneg h.1.y_mem j) hs

                                                                               
theorem GTWitness.isQuasiStrictSaddle {A : PayoffOperator ι κ} (w : GTWitness A) :
    IsQuasiStrictSaddle A w.xStar w.yStar := by
  refine ⟨w.saddle, ?_, ?_⟩
  · intro i
    by_cases hx : 0 < w.xStar i
    · exact Or.inl hx
    · right
      have hx0 : w.xStar i = 0 := by
        exact le_antisymm (le_of_not_gt hx) (simplex_nonneg w.saddle.x_mem i)
      simpa [hx0] using w.x_strictComplementary i
  · intro j
    by_cases hy : 0 < w.yStar j
    · exact Or.inl hy
    · right
      have hy0 : w.yStar j = 0 := by
        exact le_antisymm (le_of_not_gt hy) (simplex_nonneg w.saddle.y_mem j)
      simpa [hy0] using w.y_strictComplementary j

                                                                                     
theorem exists_gtWitness_iff_exists_quasiStrictSaddle (A : PayoffOperator ι κ) :
    Nonempty (GTWitness A) ↔ ∃ x : EVec ι, ∃ y : EVec κ, IsQuasiStrictSaddle A x y := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.xStar, w.yStar, w.isQuasiStrictSaddle⟩
  · rintro ⟨x, y, hxy⟩
    exact ⟨gtWitness_of_quasiStrictSaddle hxy⟩

end

end AltGDA
