import AltGDA.EuclideanMatrix
import AltGDA.Simplex.Basic

   
                       

                                                                          
                                                                            
  

open scoped BigOperators InnerProduct

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                                 
def payoff (A : PayoffOperator ι κ) (x : EVec ι) (y : EVec κ) : ℝ :=
  inner ℝ (A x) y

theorem payoff_eq_inner_adjoint (A : PayoffOperator ι κ)
    (x : EVec ι) (y : EVec κ) :
    payoff A x y = inner ℝ x (payoffAdjoint A y) := by
  exact inner_map_eq_inner_adjoint A x y

theorem payoff_eq_sum (A : PayoffOperator ι κ)
    (x : EVec ι) (y : EVec κ) :
    payoff A x y = ∑ j, (A x) j * y j := by
  simp [payoff, PiLp.inner_apply, mul_comm]

                                                                                    
theorem payoff_matrixOperator_eq (M : Matrix κ ι ℝ)
    (x : EVec ι) (y : EVec κ) :
    payoff (matrixOperator M) x y = ∑ j, y j * ∑ i, M j i * x i := by
  rw [payoff_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm]

@[simp]
theorem payoff_zero_left (A : PayoffOperator ι κ) (y : EVec κ) :
    payoff A 0 y = 0 := by
  simp [payoff]

@[simp]
theorem payoff_zero_right (A : PayoffOperator ι κ) (x : EVec ι) :
    payoff A x 0 = 0 := by
  simp [payoff]

theorem payoff_add_left (A : PayoffOperator ι κ)
    (x z : EVec ι) (y : EVec κ) :
    payoff A (x + z) y = payoff A x y + payoff A z y := by
  simp [payoff, inner_add_left]

theorem payoff_sub_left (A : PayoffOperator ι κ)
    (x z : EVec ι) (y : EVec κ) :
    payoff A (x - z) y = payoff A x y - payoff A z y := by
  simp [payoff, inner_sub_left]

theorem payoff_add_right (A : PayoffOperator ι κ)
    (x : EVec ι) (y z : EVec κ) :
    payoff A x (y + z) = payoff A x y + payoff A x z := by
  simp [payoff, inner_add_right]

theorem payoff_sub_right (A : PayoffOperator ι κ)
    (x : EVec ι) (y z : EVec κ) :
    payoff A x (y - z) = payoff A x y - payoff A x z := by
  simp [payoff, inner_sub_right]

theorem payoff_smul_left (A : PayoffOperator ι κ)
    (a : ℝ) (x : EVec ι) (y : EVec κ) :
    payoff A (a • x) y = a * payoff A x y := by
  simp [payoff, real_inner_smul_left]

theorem payoff_smul_right (A : PayoffOperator ι κ)
    (a : ℝ) (x : EVec ι) (y : EVec κ) :
    payoff A x (a • y) = a * payoff A x y := by
  simp [payoff, real_inner_smul_right]

                                                                              
def IsSaddle (A : PayoffOperator ι κ) (xStar : EVec ι) (yStar : EVec κ) : Prop :=
  xStar ∈ simplex ι ∧
    yStar ∈ simplex κ ∧
      (∀ y ∈ simplex κ, payoff A xStar y ≤ payoff A xStar yStar) ∧
        (∀ x ∈ simplex ι, payoff A xStar yStar ≤ payoff A x yStar)

theorem IsSaddle.x_mem {A : PayoffOperator ι κ} {xStar : EVec ι} {yStar : EVec κ}
    (h : IsSaddle A xStar yStar) : xStar ∈ simplex ι :=
  h.1

theorem IsSaddle.y_mem {A : PayoffOperator ι κ} {xStar : EVec ι} {yStar : EVec κ}
    (h : IsSaddle A xStar yStar) : yStar ∈ simplex κ :=
  h.2.1

theorem IsSaddle.max_inequality {A : PayoffOperator ι κ}
    {xStar : EVec ι} {yStar : EVec κ} (h : IsSaddle A xStar yStar)
    {y : EVec κ} (hy : y ∈ simplex κ) :
    payoff A xStar y ≤ payoff A xStar yStar :=
  h.2.2.1 y hy

theorem IsSaddle.min_inequality {A : PayoffOperator ι κ}
    {xStar : EVec ι} {yStar : EVec κ} (h : IsSaddle A xStar yStar)
    {x : EVec ι} (hx : x ∈ simplex ι) :
    payoff A xStar yStar ≤ payoff A x yStar :=
  h.2.2.2 x hx

                                                       
def saddleValue (A : PayoffOperator ι κ) (xStar : EVec ι) (yStar : EVec κ) : ℝ :=
  payoff A xStar yStar

end

end AltGDA
