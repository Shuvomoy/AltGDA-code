import AltGDA.EuclideanMatrix
import AltGDA.Simplex.Projection

   
                                                

                                                                               
                                                                       
            
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                           
structure GameState (ι κ : Type*) [Fintype ι] [Fintype κ] where
  x : EVec ι
  y : EVec κ
  x_mem : x ∈ simplex ι
  y_mem : y ∈ simplex κ

                                                                           
def altStep (A : PayoffOperator ι κ) (η : ℝ) (s : GameState ι κ) :
    GameState ι κ :=
  let xNext := simplexProj (s.x - η • payoffAdjoint A s.y)
  let yNext := simplexProj (s.y + η • A xNext)
  { x := xNext
    y := yNext
    x_mem := simplexProj_mem _
    y_mem := simplexProj_mem _ }

                                                                     
def trajectory (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) :
    ℕ → GameState ι κ
  | 0 => s0
  | t + 1 => altStep A η (trajectory A η s0 t)

@[simp]
theorem trajectory_zero (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) :
    trajectory A η s0 0 = s0 := by
  rfl

@[simp]
theorem trajectory_succ (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    trajectory A η s0 (t + 1) = altStep A η (trajectory A η s0 t) := by
  rfl

                                        
def xIter (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    EVec ι :=
  (trajectory A η s0 t).x

                                         
def yIter (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    EVec κ :=
  (trajectory A η s0 t).y

theorem xIter_mem (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    xIter A η s0 t ∈ simplex ι :=
  (trajectory A η s0 t).x_mem

theorem yIter_mem (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    yIter A η s0 t ∈ simplex κ :=
  (trajectory A η s0 t).y_mem

                                     
def deltaX (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    EVec ι :=
  xIter A η s0 (t + 1) - xIter A η s0 t

                                      
def deltaY (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    EVec κ :=
  yIter A η s0 (t + 1) - yIter A η s0 t

                                                        
def vField (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    EVec ι :=
  -payoffAdjoint A (yIter A η s0 t)

                                                                    
def uField (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (t : ℕ) :
    EVec κ :=
  A (xIter A η s0 (t + 1))

theorem xIter_succ_eq_projection (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    xIter A η s0 (t + 1) =
      simplexProj (xIter A η s0 t + η • vField A η s0 t) := by
  simp [xIter, yIter, trajectory, altStep, vField, sub_eq_add_neg]

theorem yIter_succ_eq_projection (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    yIter A η s0 (t + 1) =
      simplexProj (yIter A η s0 t + η • uField A η s0 t) := by
  simp [yIter, xIter, trajectory, altStep, uField]

                                                            
def avgX (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (T : ℕ) :
    EVec ι :=
  (T : ℝ)⁻¹ • ∑ t : Fin T, xIter A η s0 (t.1 + 1)

                                                             
def avgY (A : PayoffOperator ι κ) (η : ℝ) (s0 : GameState ι κ) (T : ℕ) :
    EVec κ :=
  (T : ℝ)⁻¹ • ∑ t : Fin T, yIter A η s0 (t.1 + 1)

end


end AltGDA
