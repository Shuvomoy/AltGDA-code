import AltGDA.Game.GoldmanTucker
import AltGDA.Game.TuckerAlternative

   
                                                                

                                                                    
                                                                      
                                                                          
                                                                 
  

open scoped BigOperators InnerProduct RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

                                                                 
def operatorEntry (A : PayoffOperator ι κ) (j : κ) (i : ι) : ℝ :=
  A (simplexVertex i) j

                                                                                         
theorem operator_apply_eq_sum_entries (A : PayoffOperator ι κ) (x : EVec ι) (j : κ) :
    A x j = ∑ i, operatorEntry A j i * x i := by
  have hx : x = ∑ i, x i • simplexVertex i := by
    ext k
    simp [simplexVertex_apply]
  calc
    A x j = A (∑ i, x i • simplexVertex i) j := congrArg (fun z ↦ A z j) hx
    _ = ∑ i, operatorEntry A j i * x i := by
      simp [operatorEntry, mul_comm]

                                                          
theorem adjoint_apply_eq_sum_entries (A : PayoffOperator ι κ) (y : EVec κ) (i : ι) :
    payoffAdjoint A y i = ∑ j, operatorEntry A j i * y j := by
  rw [← payoff_simplexVertex_left A i y, payoff_eq_sum]
  rfl

                                                                                   
def positiveShift (A : PayoffOperator ι κ) : ℝ := ‖A‖ + 1

                                                                  
def shiftedOperator (A : PayoffOperator ι κ) : PayoffOperator ι κ :=
  matrixOperator fun j i ↦ operatorEntry A j i + positiveShift A

theorem operatorEntry_neg_opNorm_le (A : PayoffOperator ι κ) (j : κ) (i : ι) :
    -‖A‖ ≤ operatorEntry A j i := by
  have h := abs_payoff_le_opNorm A (simplexVertex_mem i) (simplexVertex_mem j)
  simpa [operatorEntry] using neg_le_of_abs_le h

theorem shiftedEntry_pos (A : PayoffOperator ι κ) (j : κ) (i : ι) :
    0 < operatorEntry A j i + positiveShift A := by
  have h := operatorEntry_neg_opNorm_le A j i
  simp only [positiveShift]
  linarith

theorem shiftedOperator_apply (A : PayoffOperator ι κ) (x : EVec ι) (j : κ) :
    shiftedOperator A x j = A x j + positiveShift A * ∑ i, x i := by
  rw [shiftedOperator, matrixOperator_apply, operator_apply_eq_sum_entries]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem shiftedAdjoint_apply (A : PayoffOperator ι κ) (y : EVec κ) (i : ι) :
    payoffAdjoint (shiftedOperator A) y i =
      payoffAdjoint A y i + positiveShift A * ∑ j, y j := by
  rw [shiftedOperator, matrixOperator_adjoint_apply, adjoint_apply_eq_sum_entries]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

                                                                                              
theorem shiftedOperator_pos_of_nonneg_of_ne_zero (A : PayoffOperator ι κ)
    {x : EVec ι} (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) (j : κ) :
    0 < shiftedOperator A x j := by
  rw [shiftedOperator, matrixOperator_apply]
  have hex : ∃ i, 0 < x i := by
    by_contra h
    push Not at h
    apply hne
    ext i
    exact le_antisymm (h i) (hx i)
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (le_of_lt (shiftedEntry_pos A j k)) (hx k)
  · exact ⟨i, Finset.mem_univ i, mul_pos (shiftedEntry_pos A j i) hi⟩

                                                                           
abbrev GameHomIndex (ι κ : Type*) := Sum ι (Sum κ Unit)

                                                                  
def homX (z : EVec (GameHomIndex ι κ)) : EVec ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm fun i ↦ z (Sum.inl i)

                                                                  
def homY (z : EVec (GameHomIndex ι κ)) : EVec κ :=
  (WithLp.equiv 2 (κ → ℝ)).symm fun j ↦ z (Sum.inr (Sum.inl j))

                                                                
def homT (z : EVec (GameHomIndex ι κ)) : ℝ :=
  z (Sum.inr (Sum.inr Unit.unit))

@[simp]
theorem homX_apply (z : EVec (GameHomIndex ι κ)) (i : ι) :
    homX z i = z (Sum.inl i) :=
  rfl

@[simp]
theorem homY_apply (z : EVec (GameHomIndex ι κ)) (j : κ) :
    homY z j = z (Sum.inr (Sum.inl j)) :=
  rfl

                                                                               
def gameSkewMatrix (B : PayoffOperator ι κ) :
    Matrix (GameHomIndex ι κ) (GameHomIndex ι κ) ℝ
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl i, Sum.inr (Sum.inl j) => operatorEntry B j i
  | Sum.inl _, Sum.inr (Sum.inr _) => -1
  | Sum.inr (Sum.inl j), Sum.inl i => -operatorEntry B j i
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 1
  | Sum.inr (Sum.inr _), Sum.inl _ => 1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => 0

                                            
def gameSkewOperator (B : PayoffOperator ι κ) :
    PayoffOperator (GameHomIndex ι κ) (GameHomIndex ι κ) :=
  matrixOperator (gameSkewMatrix B)

theorem gameSkewMatrix_transpose (B : PayoffOperator ι κ) :
    (gameSkewMatrix B).transpose = -gameSkewMatrix B := by
  ext a b
  rcases a with i | j <;> rcases b with i' | j'
  · simp [gameSkewMatrix, Matrix.transpose_apply]
  · rcases j' with j' | t <;> simp [gameSkewMatrix, Matrix.transpose_apply]
  · rcases j with j | t <;> simp [gameSkewMatrix, Matrix.transpose_apply]
  · rcases j with j | t <;> rcases j' with j' | t' <;>
      simp [gameSkewMatrix, Matrix.transpose_apply]

theorem gameSkewOperator_adjoint (B : PayoffOperator ι κ) :
    payoffAdjoint (gameSkewOperator B) = -gameSkewOperator B := by
  rw [gameSkewOperator, matrixOperator_adjoint, gameSkewMatrix_transpose]
  ext z a
  simp [matrixOperator_apply]

theorem gameSkewOperator_apply_x (B : PayoffOperator ι κ)
    (z : EVec (GameHomIndex ι κ)) (i : ι) :
    gameSkewOperator B z (Sum.inl i) = payoffAdjoint B (homY z) i - homT z := by
  rw [gameSkewOperator, matrixOperator_apply, adjoint_apply_eq_sum_entries]
  simp [gameSkewMatrix, homT]
  ring

theorem gameSkewOperator_apply_y (B : PayoffOperator ι κ)
    (z : EVec (GameHomIndex ι κ)) (j : κ) :
    gameSkewOperator B z (Sum.inr (Sum.inl j)) = homT z - B (homX z) j := by
  rw [gameSkewOperator, matrixOperator_apply, operator_apply_eq_sum_entries]
  simp [gameSkewMatrix, homT]
  ring

theorem gameSkewOperator_apply_t (B : PayoffOperator ι κ)
    (z : EVec (GameHomIndex ι κ)) :
    gameSkewOperator B z (Sum.inr (Sum.inr Unit.unit)) =
      (∑ i, homX z i) - ∑ j, homY z j := by
  simp [gameSkewOperator, gameSkewMatrix, matrixOperator_apply]
  ring

                                          
def homMassX (z : EVec (GameHomIndex ι κ)) : ℝ := ∑ i, homX z i

                                          
def homMassY (z : EVec (GameHomIndex ι κ)) : ℝ := ∑ j, homY z j

theorem homX_eq_zero_of_nonneg_of_mass_eq_zero
    {z : EVec (GameHomIndex ι κ)} (hx : ∀ i, 0 ≤ homX z i)
    (hmass : homMassX z = 0) : homX z = 0 := by
  ext i
  change homX z i = 0
  apply le_antisymm
  · rw [homMassX] at hmass
    have hle : homX z i ≤ ∑ k, homX z k :=
      Finset.single_le_sum (fun k _ ↦ hx k) (Finset.mem_univ i)
    linarith
  · exact hx i

theorem homY_eq_zero_of_nonneg_of_mass_eq_zero
    {z : EVec (GameHomIndex ι κ)} (hy : ∀ j, 0 ≤ homY z j)
    (hmass : homMassY z = 0) : homY z = 0 := by
  ext j
  change homY z j = 0
  apply le_antisymm
  · rw [homMassY] at hmass
    have hle : homY z j ≤ ∑ k, homY z k :=
      Finset.single_le_sum (fun k _ ↦ hy k) (Finset.mem_univ j)
    linarith
  · exact hy j

                                                                                        
theorem homT_pos_of_skewData (B : PayoffOperator ι κ)
    (hBpos : ∀ {x : EVec ι}, (∀ i, 0 ≤ x i) → x ≠ 0 → ∀ j, 0 < B x j)
    (z : EVec (GameHomIndex ι κ))
    (hz : ∀ a, 0 ≤ z a)
    (hw : ∀ a, 0 ≤ gameSkewOperator B z a)
    (hstrict : ∀ a, 0 < z a + gameSkewOperator B z a) :
    0 < homT z := by
  have ht_nonneg : 0 ≤ homT z := hz _
  rcases ht_nonneg.eq_or_lt with ht0 | htpos
  · exfalso
    have htzero : homT z = 0 := ht0.symm
    have hx_nonneg : ∀ i, 0 ≤ homX z i := fun i ↦ hz _
    have hy_nonneg : ∀ j, 0 ≤ homY z j := fun j ↦ hz _
    have hx0 : homX z = 0 := by
      by_contra hxne
      let j : κ := Classical.choice inferInstance
      have hpositive := hBpos hx_nonneg hxne j
      have hwy := hw (Sum.inr (Sum.inl j))
      rw [gameSkewOperator_apply_y, htzero] at hwy
      linarith
    have hmx0 : homMassX z = 0 := by simp [homMassX, hx0]
    have hmy_nonneg : 0 ≤ homMassY z := by
      exact Finset.sum_nonneg fun j _ ↦ hy_nonneg j
    have hwt := hw (Sum.inr (Sum.inr Unit.unit))
    rw [gameSkewOperator_apply_t, ← homMassX, ← homMassY, hmx0] at hwt
    have hmy0 : homMassY z = 0 := by linarith
    have hy0 : homY z = 0 := homY_eq_zero_of_nonneg_of_mass_eq_zero hy_nonneg hmy0
    have hs := hstrict (Sum.inr (Sum.inr Unit.unit))
    rw [gameSkewOperator_apply_t, ← homMassX, ← homMassY] at hs
    have hs' : 0 < homT z + (homMassX z - homMassY z) := by
      simpa [homT] using hs
    rw [htzero, hmx0, hmy0] at hs'
    linarith
  · exact htpos

                                                                              
                                                                                     
theorem homMass_pos_and_eq_of_skewData (B : PayoffOperator ι κ)
    (hBpos : ∀ {x : EVec ι}, (∀ i, 0 ≤ x i) → x ≠ 0 → ∀ j, 0 < B x j)
    (z : EVec (GameHomIndex ι κ))
    (hz : ∀ a, 0 ≤ z a)
    (hw : ∀ a, 0 ≤ gameSkewOperator B z a)
    (hcomp : ∀ a, z a * gameSkewOperator B z a = 0)
    (hstrict : ∀ a, 0 < z a + gameSkewOperator B z a) :
    0 < homMassX z ∧ homMassX z = homMassY z := by
  have htpos := homT_pos_of_skewData B hBpos z hz hw hstrict
  have hct := hcomp (Sum.inr (Sum.inr Unit.unit))
  rw [gameSkewOperator_apply_t, ← homMassX, ← homMassY] at hct
  have hct' : homT z * (homMassX z - homMassY z) = 0 := by
    simpa [homT] using hct
  have hmass_eq : homMassX z = homMassY z := by
    have : homMassX z - homMassY z = 0 :=
      (mul_eq_zero.mp hct').resolve_left (ne_of_gt htpos)
    linarith
  refine ⟨?_, hmass_eq⟩
  have hx_nonneg : ∀ i, 0 ≤ homX z i := fun i ↦ hz _
  have hmx_nonneg : 0 ≤ homMassX z :=
    Finset.sum_nonneg fun i _ ↦ hx_nonneg i
  rcases hmx_nonneg.eq_or_lt with hmx0 | hmxpos
  · exfalso
    have hmxzero : homMassX z = 0 := hmx0.symm
    have hmyzero : homMassY z = 0 := by rw [← hmass_eq, hmxzero]
    have hy_nonneg : ∀ j, 0 ≤ homY z j := fun j ↦ hz _
    have hyzero := homY_eq_zero_of_nonneg_of_mass_eq_zero hy_nonneg hmyzero
    have i : ι := Classical.choice inferInstance
    have hwi := hw (Sum.inl i)
    rw [gameSkewOperator_apply_x, hyzero] at hwi
    simp only [map_zero, PiLp.zero_apply, zero_sub] at hwi
    linarith
  · exact hmxpos

                                                         
def normalizedHomX (z : EVec (GameHomIndex ι κ)) : EVec ι :=
  (homMassX z)⁻¹ • homX z

                                                                
def normalizedHomY (z : EVec (GameHomIndex ι κ)) : EVec κ :=
  (homMassX z)⁻¹ • homY z

                                    
def normalizedHomValue (z : EVec (GameHomIndex ι κ)) : ℝ :=
  (homMassX z)⁻¹ * homT z

@[simp]
theorem normalizedHomX_apply (z : EVec (GameHomIndex ι κ)) (i : ι) :
    normalizedHomX z i = (homMassX z)⁻¹ * homX z i := by
  simp [normalizedHomX]

@[simp]
theorem normalizedHomY_apply (z : EVec (GameHomIndex ι κ)) (j : κ) :
    normalizedHomY z j = (homMassX z)⁻¹ * homY z j := by
  simp [normalizedHomY]

theorem normalizedHomX_mem_simplex {z : EVec (GameHomIndex ι κ)}
    (hz : ∀ a, 0 ≤ z a) (hmass : 0 < homMassX z) :
    normalizedHomX z ∈ simplex ι := by
  rw [mem_simplex_iff]
  constructor
  · intro i
    exact mul_nonneg (le_of_lt (inv_pos.mpr hmass)) (hz _)
  · simp_rw [normalizedHomX_apply]
    rw [← Finset.mul_sum]
    change (homMassX z)⁻¹ * homMassX z = 1
    exact inv_mul_cancel₀ (ne_of_gt hmass)

theorem normalizedHomY_mem_simplex {z : EVec (GameHomIndex ι κ)}
    (hz : ∀ a, 0 ≤ z a) (hmass : 0 < homMassX z)
    (hmass_eq : homMassX z = homMassY z) : normalizedHomY z ∈ simplex κ := by
  rw [mem_simplex_iff]
  constructor
  · intro j
    exact mul_nonneg (le_of_lt (inv_pos.mpr hmass)) (hz _)
  · simp_rw [normalizedHomY_apply]
    rw [← Finset.mul_sum]
    change (homMassX z)⁻¹ * homMassY z = 1
    rw [← hmass_eq]
    exact inv_mul_cancel₀ (ne_of_gt hmass)

                                                                                
theorem normalized_xSlack_apply (B : PayoffOperator ι κ)
    (z : EVec (GameHomIndex ι κ)) (i : ι) :
    xSlackAt B (normalizedHomY z) (normalizedHomValue z) i =
      (homMassX z)⁻¹ * gameSkewOperator B z (Sum.inl i) := by
  rw [xSlackAt_apply, gameSkewOperator_apply_x]
  simp only [normalizedHomY, normalizedHomValue, map_smul, PiLp.smul_apply,
    smul_eq_mul]
  ring

                                                                                 
theorem normalized_ySlack_apply (B : PayoffOperator ι κ)
    (z : EVec (GameHomIndex ι κ)) (j : κ) :
    ySlackAt B (normalizedHomX z) (normalizedHomValue z) j =
      (homMassX z)⁻¹ * gameSkewOperator B z (Sum.inr (Sum.inl j)) := by
  rw [ySlackAt_apply, gameSkewOperator_apply_y]
  simp only [normalizedHomX, normalizedHomValue, map_smul, PiLp.smul_apply,
    smul_eq_mul]
  ring

                                                                        
theorem normalizedHom_isSaddle (B : PayoffOperator ι κ)
    (z : EVec (GameHomIndex ι κ))
    (hz : ∀ a, 0 ≤ z a)
    (hw : ∀ a, 0 ≤ gameSkewOperator B z a)
    (hmass : 0 < homMassX z) (hmass_eq : homMassX z = homMassY z) :
    IsSaddle B (normalizedHomX z) (normalizedHomY z) := by
  have hxmem := normalizedHomX_mem_simplex (z := z) hz hmass
  have hymem := normalizedHomY_mem_simplex hz hmass hmass_eq
  have hinv_nonneg : 0 ≤ (homMassX z)⁻¹ := le_of_lt (inv_pos.mpr hmass)
  have hu : upperValue B (normalizedHomX z) ≤ normalizedHomValue z := by
    rw [upperValue_le_iff]
    intro j
    have h := mul_nonneg hinv_nonneg (hw (Sum.inr (Sum.inl j)))
    rw [← normalized_ySlack_apply] at h
    simp only [ySlackAt_apply] at h
    linarith
  have hl : normalizedHomValue z ≤ lowerValue B (normalizedHomY z) := by
    rw [le_lowerValue_iff]
    intro i
    have h := mul_nonneg hinv_nonneg (hw (Sum.inl i))
    rw [← normalized_xSlack_apply] at h
    simp only [xSlackAt_apply] at h
    linarith
  rw [isSaddle_iff_dualityGap_eq_zero B hxmem hymem]
  have hgap := dualityGap_nonneg B hxmem hymem
  unfold dualityGap at hgap ⊢
  linarith

theorem normalizedHom_saddleValue (B : PayoffOperator ι κ)
    (z : EVec (GameHomIndex ι κ))
    (hz : ∀ a, 0 ≤ z a)
    (hw : ∀ a, 0 ≤ gameSkewOperator B z a)
    (hmass : 0 < homMassX z) (hmass_eq : homMassX z = homMassY z) :
    saddleValue B (normalizedHomX z) (normalizedHomY z) = normalizedHomValue z := by
  have hs := normalizedHom_isSaddle B z hz hw hmass hmass_eq
  have hupper := hs.upperValue_eq_payoff
  have hlower := hs.lowerValue_eq_payoff
  have hinv_nonneg : 0 ≤ (homMassX z)⁻¹ := le_of_lt (inv_pos.mpr hmass)
  have hu : upperValue B (normalizedHomX z) ≤ normalizedHomValue z := by
    rw [upperValue_le_iff]
    intro j
    have h := mul_nonneg hinv_nonneg (hw (Sum.inr (Sum.inl j)))
    rw [← normalized_ySlack_apply] at h
    simp only [ySlackAt_apply] at h
    linarith
  have hl : normalizedHomValue z ≤ lowerValue B (normalizedHomY z) := by
    rw [le_lowerValue_iff]
    intro i
    have h := mul_nonneg hinv_nonneg (hw (Sum.inl i))
    rw [← normalized_xSlack_apply] at h
    simp only [xSlackAt_apply] at h
    linarith
  unfold saddleValue
  linarith

                                                                  
                                  
def gtWitness_of_skewData (B : PayoffOperator ι κ)
    (hBpos : ∀ {x : EVec ι}, (∀ i, 0 ≤ x i) → x ≠ 0 → ∀ j, 0 < B x j)
    (z : EVec (GameHomIndex ι κ))
    (hz : ∀ a, 0 ≤ z a)
    (hw : ∀ a, 0 ≤ gameSkewOperator B z a)
    (hcomp : ∀ a, z a * gameSkewOperator B z a = 0)
    (hstrict : ∀ a, 0 < z a + gameSkewOperator B z a) : GTWitness B := by
  obtain ⟨hmass, hmass_eq⟩ :=
    homMass_pos_and_eq_of_skewData B hBpos z hz hw hcomp hstrict
  have hs := normalizedHom_isSaddle B z hz hw hmass hmass_eq
  have hvalue := normalizedHom_saddleValue B z hz hw hmass hmass_eq
  have hinvpos : 0 < (homMassX z)⁻¹ := inv_pos.mpr hmass
  refine
    { xStar := normalizedHomX z
      yStar := normalizedHomY z
      saddle := hs
      xSlack_nonneg := ?_
      ySlack_nonneg := ?_
      x_complementary := ?_
      y_complementary := ?_
      x_strictComplementary := ?_
      y_strictComplementary := ?_ }
  · intro i
    rw [hvalue, normalized_xSlack_apply]
    exact mul_nonneg (le_of_lt hinvpos) (hw _)
  · intro j
    rw [hvalue, normalized_ySlack_apply]
    exact mul_nonneg (le_of_lt hinvpos) (hw _)
  · intro i
    rw [hvalue, normalizedHomX_apply, normalized_xSlack_apply]
    rw [homX_apply]
    calc
      (homMassX z)⁻¹ * z (Sum.inl i) *
          ((homMassX z)⁻¹ * gameSkewOperator B z (Sum.inl i)) =
          (homMassX z)⁻¹ * (homMassX z)⁻¹ *
            (z (Sum.inl i) * gameSkewOperator B z (Sum.inl i)) := by ring
      _ = 0 := by rw [hcomp]; ring
  · intro j
    rw [hvalue, normalizedHomY_apply, normalized_ySlack_apply]
    rw [homY_apply]
    calc
      (homMassX z)⁻¹ * z (Sum.inr (Sum.inl j)) *
          ((homMassX z)⁻¹ * gameSkewOperator B z (Sum.inr (Sum.inl j))) =
          (homMassX z)⁻¹ * (homMassX z)⁻¹ *
            (z (Sum.inr (Sum.inl j)) *
              gameSkewOperator B z (Sum.inr (Sum.inl j))) := by ring
      _ = 0 := by rw [hcomp]; ring
  · intro i
    rw [hvalue, normalizedHomX_apply, normalized_xSlack_apply]
    rw [homX_apply]
    calc
      0 < (homMassX z)⁻¹ *
          (z (Sum.inl i) + gameSkewOperator B z (Sum.inl i)) :=
        mul_pos hinvpos (hstrict _)
      _ = (homMassX z)⁻¹ * z (Sum.inl i) +
          (homMassX z)⁻¹ * gameSkewOperator B z (Sum.inl i) := by ring
  · intro j
    rw [hvalue, normalizedHomY_apply, normalized_ySlack_apply]
    rw [homY_apply]
    calc
      0 < (homMassX z)⁻¹ *
          (z (Sum.inr (Sum.inl j)) +
            gameSkewOperator B z (Sum.inr (Sum.inl j))) :=
        mul_pos hinvpos (hstrict _)
      _ = (homMassX z)⁻¹ * z (Sum.inr (Sum.inl j)) +
          (homMassX z)⁻¹ * gameSkewOperator B z (Sum.inr (Sum.inl j)) := by ring

                                                                           
                             
theorem payoff_shiftedOperator (A : PayoffOperator ι κ) (x : EVec ι) (y : EVec κ) :
    payoff (shiftedOperator A) x y =
      payoff A x y + positiveShift A * (∑ i, x i) * ∑ j, y j := by
  rw [payoff_eq_sum, payoff_eq_sum]
  simp_rw [shiftedOperator_apply, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

                                                                        
            
theorem payoff_shiftedOperator_of_mem (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    payoff (shiftedOperator A) x y = payoff A x y + positiveShift A := by
  rw [payoff_shiftedOperator, sum_eq_one_of_mem_simplex hx,
    sum_eq_one_of_mem_simplex hy]
  ring

                                                                 
theorem isSaddle_shiftedOperator_iff (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} :
    IsSaddle (shiftedOperator A) x y ↔ IsSaddle A x y := by
  constructor
  · intro hs
    refine ⟨hs.x_mem, hs.y_mem, ?_, ?_⟩
    · intro y' hy'
      have h := hs.max_inequality hy'
      rw [payoff_shiftedOperator_of_mem A hs.x_mem hy',
        payoff_shiftedOperator_of_mem A hs.x_mem hs.y_mem] at h
      linarith
    · intro x' hx'
      have h := hs.min_inequality hx'
      rw [payoff_shiftedOperator_of_mem A hs.x_mem hs.y_mem,
        payoff_shiftedOperator_of_mem A hx' hs.y_mem] at h
      linarith
  · intro hs
    refine ⟨hs.x_mem, hs.y_mem, ?_, ?_⟩
    · intro y' hy'
      have h := hs.max_inequality hy'
      rw [payoff_shiftedOperator_of_mem A hs.x_mem hy',
        payoff_shiftedOperator_of_mem A hs.x_mem hs.y_mem]
      linarith
    · intro x' hx'
      have h := hs.min_inequality hx'
      rw [payoff_shiftedOperator_of_mem A hs.x_mem hs.y_mem,
        payoff_shiftedOperator_of_mem A hx' hs.y_mem]
      linarith

theorem saddleValue_shiftedOperator_of_mem (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    saddleValue (shiftedOperator A) x y =
      saddleValue A x y + positiveShift A := by
  exact payoff_shiftedOperator_of_mem A hx hy

                                                                         
theorem xSlackAt_shiftedOperator_eq (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    xSlackAt (shiftedOperator A) y (saddleValue (shiftedOperator A) x y) =
      xSlackAt A y (saddleValue A x y) := by
  ext i
  rw [xSlackAt_apply, xSlackAt_apply, shiftedAdjoint_apply,
    sum_eq_one_of_mem_simplex hy, saddleValue_shiftedOperator_of_mem A hx hy]
  ring

                                                                         
theorem ySlackAt_shiftedOperator_eq (A : PayoffOperator ι κ)
    {x : EVec ι} {y : EVec κ} (hx : x ∈ simplex ι) (hy : y ∈ simplex κ) :
    ySlackAt (shiftedOperator A) x (saddleValue (shiftedOperator A) x y) =
      ySlackAt A x (saddleValue A x y) := by
  ext j
  rw [ySlackAt_apply, ySlackAt_apply, shiftedOperator_apply,
    sum_eq_one_of_mem_simplex hx, saddleValue_shiftedOperator_of_mem A hx hy]
  ring

                                                                          
def shiftBackGTWitness (A : PayoffOperator ι κ)
    (w : GTWitness (shiftedOperator A)) : GTWitness A := by
  have hsA : IsSaddle A w.xStar w.yStar :=
    (isSaddle_shiftedOperator_iff A).mp w.saddle
  have hq := w.isQuasiStrictSaddle
  apply gtWitness_of_quasiStrictSaddle
  refine ⟨hsA, ?_, ?_⟩
  · intro i
    rcases hq.2.1 i with hxi | hsi
    · exact Or.inl hxi
    · right
      rw [← xSlackAt_shiftedOperator_eq A w.saddle.x_mem w.saddle.y_mem]
      exact hsi
  · intro j
    rcases hq.2.2 j with hyj | hsj
    · exact Or.inl hyj
    · right
      rw [← ySlackAt_shiftedOperator_eq A w.saddle.x_mem w.saddle.y_mem]
      exact hsj

                                                                          
theorem exists_gtWitness (A : PayoffOperator ι κ) : Nonempty (GTWitness A) := by
  obtain ⟨z, hz, hw, hcomp, hstrict⟩ :=
    skew_strict_complementarity (gameSkewOperator (shiftedOperator A))
      (gameSkewOperator_adjoint (shiftedOperator A))
  exact ⟨shiftBackGTWitness A
    (gtWitness_of_skewData (shiftedOperator A)
      (shiftedOperator_pos_of_nonneg_of_ne_zero A) z hz hw hcomp hstrict)⟩

end

end AltGDA
