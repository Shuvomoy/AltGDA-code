import AltGDA.Game.Basic

   
                                         

                                                                            
                                                                            
                                         

                                                                             
                                                                           
                                                                          
                                             
  

open scoped BigOperators InnerProduct

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                           
def xSlackAt (A : PayoffOperator ι κ) (y : EVec κ) (ν : ℝ) : EVec ι :=
  payoffAdjoint A y - ν • ones ι

                                                                             
def ySlackAt (A : PayoffOperator ι κ) (x : EVec ι) (ν : ℝ) : EVec κ :=
  ν • ones κ - A x

@[simp]
theorem xSlackAt_apply (A : PayoffOperator ι κ) (y : EVec κ) (ν : ℝ) (i : ι) :
    xSlackAt A y ν i = payoffAdjoint A y i - ν := by
  simp [xSlackAt]

@[simp]
theorem ySlackAt_apply (A : PayoffOperator ι κ) (x : EVec ι) (ν : ℝ) (j : κ) :
    ySlackAt A x ν j = ν - A x j := by
  simp [ySlackAt]

   
                                          

                                                                           
                                                                             
                                                                   
                    
  
structure GTWitness (A : PayoffOperator ι κ) where
  xStar : EVec ι
  yStar : EVec κ
  saddle : IsSaddle A xStar yStar
  xSlack_nonneg : ∀ i, 0 ≤ xSlackAt A yStar (saddleValue A xStar yStar) i
  ySlack_nonneg : ∀ j, 0 ≤ ySlackAt A xStar (saddleValue A xStar yStar) j
  x_complementary :
    ∀ i, xStar i * xSlackAt A yStar (saddleValue A xStar yStar) i = 0
  y_complementary :
    ∀ j, yStar j * ySlackAt A xStar (saddleValue A xStar yStar) j = 0
  x_strictComplementary :
    ∀ i, 0 < xStar i + xSlackAt A yStar (saddleValue A xStar yStar) i
  y_strictComplementary :
    ∀ j, 0 < yStar j + ySlackAt A xStar (saddleValue A xStar yStar) j

namespace GTWitness

variable {A : PayoffOperator ι κ} (w : GTWitness A)

                                                     
def value : ℝ := saddleValue A w.xStar w.yStar

                                                                   
def slackX : EVec ι := xSlackAt A w.yStar w.value

                                                                
def slackY : EVec κ := ySlackAt A w.xStar w.value

                                                      
def supportX : Finset ι :=
  Finset.univ.filter fun i ↦ 0 < w.xStar i

                                                      
def supportY : Finset κ :=
  Finset.univ.filter fun j ↦ 0 < w.yStar j

                                                          
def offSupportX : Finset ι :=
  Finset.univ \ w.supportX

                                                          
def offSupportY : Finset κ :=
  Finset.univ \ w.supportY

theorem x_mem : w.xStar ∈ simplex ι :=
  w.saddle.x_mem

theorem y_mem : w.yStar ∈ simplex κ :=
  w.saddle.y_mem

@[simp]
theorem slackX_apply (i : ι) :
    w.slackX i = payoffAdjoint A w.yStar i - w.value := by
  simp [slackX]

@[simp]
theorem slackY_apply (j : κ) :
    w.slackY j = w.value - A w.xStar j := by
  simp [slackY]

@[simp]
theorem payoff_at_witness : payoff A w.xStar w.yStar = w.value := by
  rfl

                                                                              
theorem adjoint_eq_value_ones_add_slackX :
    payoffAdjoint A w.yStar = w.value • ones ι + w.slackX := by
  simp only [slackX, xSlackAt]
  abel

                                                                    
theorem map_eq_value_ones_sub_slackY :
    A w.xStar = w.value • ones κ - w.slackY := by
  simp only [slackY, ySlackAt]
  abel

theorem adjoint_apply_eq_value_add_slackX (i : ι) :
    payoffAdjoint A w.yStar i = w.value + w.slackX i := by
  rw [w.adjoint_eq_value_ones_add_slackX]
  simp

theorem map_apply_eq_value_sub_slackY (j : κ) :
    A w.xStar j = w.value - w.slackY j := by
  rw [w.map_eq_value_ones_sub_slackY]
  simp

theorem slackX_nonneg (i : ι) : 0 ≤ w.slackX i := by
  exact w.xSlack_nonneg i

theorem slackY_nonneg (j : κ) : 0 ≤ w.slackY j := by
  exact w.ySlack_nonneg j

theorem x_mul_slackX (i : ι) : w.xStar i * w.slackX i = 0 := by
  exact w.x_complementary i

theorem y_mul_slackY (j : κ) : w.yStar j * w.slackY j = 0 := by
  exact w.y_complementary j

theorem x_add_slackX_pos (i : ι) : 0 < w.xStar i + w.slackX i := by
  exact w.x_strictComplementary i

theorem y_add_slackY_pos (j : κ) : 0 < w.yStar j + w.slackY j := by
  exact w.y_strictComplementary j

@[simp]
theorem mem_supportX {i : ι} : i ∈ w.supportX ↔ 0 < w.xStar i := by
  simp [supportX]

@[simp]
theorem mem_supportY {j : κ} : j ∈ w.supportY ↔ 0 < w.yStar j := by
  simp [supportY]

theorem mem_supportX_iff_ne_zero {i : ι} :
    i ∈ w.supportX ↔ w.xStar i ≠ 0 := by
  rw [mem_supportX]
  constructor
  · exact ne_of_gt
  · intro hne
    exact lt_of_le_of_ne (nonneg_of_mem_simplex w.x_mem i) hne.symm

theorem mem_supportY_iff_ne_zero {j : κ} :
    j ∈ w.supportY ↔ w.yStar j ≠ 0 := by
  rw [mem_supportY]
  constructor
  · exact ne_of_gt
  · intro hne
    exact lt_of_le_of_ne (nonneg_of_mem_simplex w.y_mem j) hne.symm

@[simp]
theorem mem_offSupportX {i : ι} : i ∈ w.offSupportX ↔ w.xStar i = 0 := by
  rw [offSupportX, Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and, mem_supportX, not_lt]
  constructor
  · intro h
    exact le_antisymm h (nonneg_of_mem_simplex w.x_mem i)
  · intro h
    simpa [h]

@[simp]
theorem mem_offSupportY {j : κ} : j ∈ w.offSupportY ↔ w.yStar j = 0 := by
  rw [offSupportY, Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and, mem_supportY, not_lt]
  constructor
  · intro h
    exact le_antisymm h (nonneg_of_mem_simplex w.y_mem j)
  · intro h
    simpa [h]

theorem supportX_nonempty : w.supportX.Nonempty := by
  obtain ⟨i, hi⟩ := exists_pos_of_mem_simplex w.x_mem
  exact ⟨i, (w.mem_supportX).mpr hi⟩

theorem supportY_nonempty : w.supportY.Nonempty := by
  obtain ⟨j, hj⟩ := exists_pos_of_mem_simplex w.y_mem
  exact ⟨j, (w.mem_supportY).mpr hj⟩

theorem slackX_eq_zero_of_mem_support {i : ι} (hi : i ∈ w.supportX) :
    w.slackX i = 0 := by
  rcases mul_eq_zero.mp (w.x_mul_slackX i) with hx | hs
  · exact (ne_of_gt ((w.mem_supportX).mp hi) hx).elim
  · exact hs

theorem slackY_eq_zero_of_mem_support {j : κ} (hj : j ∈ w.supportY) :
    w.slackY j = 0 := by
  rcases mul_eq_zero.mp (w.y_mul_slackY j) with hy | hs
  · exact (ne_of_gt ((w.mem_supportY).mp hj) hy).elim
  · exact hs

theorem slackX_pos_of_mem_offSupport {i : ι} (hi : i ∈ w.offSupportX) :
    0 < w.slackX i := by
  have hx : w.xStar i = 0 := (w.mem_offSupportX).mp hi
  simpa [hx] using w.x_add_slackX_pos i

theorem slackY_pos_of_mem_offSupport {j : κ} (hj : j ∈ w.offSupportY) :
    0 < w.slackY j := by
  have hy : w.yStar j = 0 := (w.mem_offSupportY).mp hj
  simpa [hy] using w.y_add_slackY_pos j

theorem mem_supportX_iff_slackX_eq_zero {i : ι} :
    i ∈ w.supportX ↔ w.slackX i = 0 := by
  constructor
  · exact w.slackX_eq_zero_of_mem_support
  · intro hs
    by_contra hi
    have hoff : i ∈ w.offSupportX := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
    exact (ne_of_gt (w.slackX_pos_of_mem_offSupport hoff)) hs

theorem mem_supportY_iff_slackY_eq_zero {j : κ} :
    j ∈ w.supportY ↔ w.slackY j = 0 := by
  constructor
  · exact w.slackY_eq_zero_of_mem_support
  · intro hs
    by_contra hj
    have hoff : j ∈ w.offSupportY := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
    exact (ne_of_gt (w.slackY_pos_of_mem_offSupport hoff)) hs

end GTWitness

end

end AltGDA
