import AltGDA.Simplex.Basic
import AltGDA.EuclideanMatrix

   
                                          

                                                           
                                                              
                                                                      
                                                                            
  

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

                                                          
def strictPositiveOrthant (ι : Type*) [Fintype ι] : Set (EVec ι) :=
  {x | ∀ i, 0 < x i}

@[simp]
theorem mem_strictPositiveOrthant_iff {x : EVec ι} :
    x ∈ strictPositiveOrthant ι ↔ ∀ i, 0 < x i :=
  Iff.rfl

theorem strictPositiveOrthant_isOpen : IsOpen (strictPositiveOrthant ι) := by
  simp only [strictPositiveOrthant, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)

theorem strictPositiveOrthant_convex : Convex ℝ (strictPositiveOrthant ι) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hxa := hx i
  have hyb := hy i
  rcases ha.eq_or_lt with rfl | ha'
  · have hb' : 0 < b := by linarith
    simpa using mul_pos hb' hyb
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hxa) (mul_nonneg hb hyb.le)

private theorem inner_simplexVertex_right (v : EVec ι) (i : ι) :
    ⟪v, simplexVertex i⟫ = v i := by
  classical
  rw [PiLp.inner_apply]
  simp [simplexVertex_apply]

   
                                                                    
                                                                       
      
  
theorem strictPositive_or_nonnegative_orthogonal (L : Submodule ℝ (EVec ι)) :
    (∃ z : EVec ι, z ∈ L ∧ ∀ i, 0 < z i) ∨
      ∃ s : EVec ι, s ∈ Lᗮ ∧ (∀ i, 0 ≤ s i) ∧ s ≠ 0 := by
  classical
  by_cases hpos : ∃ z : EVec ι, z ∈ L ∧ ∀ i, 0 < z i
  · exact Or.inl hpos
  · right
    have hdisj : Disjoint (strictPositiveOrthant ι) (L : Set (EVec ι)) := by
      rw [Set.disjoint_left]
      intro z hzpos hzL
      exact hpos ⟨z, hzL, hzpos⟩
    obtain ⟨f, u, hfpos, hfL⟩ := geometric_hahn_banach_open
      strictPositiveOrthant_convex strictPositiveOrthant_isOpen L.convex hdisj
    have hu0 : u ≤ 0 := by
      simpa using hfL 0 L.zero_mem
    have hones : ones ι ∈ strictPositiveOrthant ι := by
      intro i
      simp
    have hfone : f (ones ι) < 0 :=
      (hfpos (ones ι) hones).trans_le hu0
    have hfLzero : ∀ z ∈ L, f z = 0 := by
      intro z hz
      by_contra hn
      let a : ℝ := (u - 1) / f z
      have haz : a • z ∈ L := L.smul_mem a hz
      have hsep := hfL (a • z) haz
      have hfa : f (a • z) = u - 1 := by
        simp only [map_smul, smul_eq_mul, a]
        exact div_mul_cancel₀ (u - 1) hn
      rw [hfa] at hsep
      linarith

    let r : EVec ι := (InnerProductSpace.toDual ℝ (EVec ι)).symm f
    have hr_eval : ∀ x : EVec ι, ⟪r, x⟫ = f x := by
      intro x
      exact InnerProductSpace.toDual_symm_apply
    have hf_vertex_nonpos : ∀ i, f (simplexVertex i) ≤ 0 := by
      intro i
      by_contra hnot
      have hfi : 0 < f (simplexVertex i) := lt_of_not_ge hnot
      let ε : ℝ := f (simplexVertex i) / (-2 * f (ones ι))
      have hden : 0 < -2 * f (ones ι) := mul_pos_of_neg_of_neg (by norm_num) hfone
      have hε : 0 < ε := div_pos hfi hden
      let q : EVec ι := simplexVertex i + ε • ones ι
      have hqpos : q ∈ strictPositiveOrthant ι := by
        intro j
        simp only [q, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ones_apply,
          simplexVertex_apply]
        split_ifs <;> linarith
      have hfqneg : f q < 0 := (hfpos q hqpos).trans_le hu0
      have hfq : f q = f (simplexVertex i) / 2 := by
        simp only [q, map_add, map_smul, smul_eq_mul, ε]
        field_simp [ne_of_lt hfone]
        ring
      rw [hfq] at hfqneg
      linarith
    let s : EVec ι := -r
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [Submodule.mem_orthogonal']
      intro z hz
      simp only [s, inner_neg_left, hr_eval]
      rw [hfLzero z hz]
      simp
    · intro i
      have hcoord : r i = f (simplexVertex i) := by
        rw [← inner_simplexVertex_right r i]
        exact hr_eval (simplexVertex i)
      simp only [s, PiLp.neg_apply]
      rw [hcoord]
      exact neg_nonneg.mpr (hf_vertex_nonpos i)
    · intro hs
      have hrzero : r = 0 := by simpa [s] using congrArg Neg.neg hs
      have : f (ones ι) = 0 := by
        rw [← hr_eval (ones ι), hrzero]
        simp
      linarith

                                                                           
                                        
def AttainableCoordinate (L : Submodule ℝ (EVec ι)) (i : ι) : Prop :=
  ∃ z : EVec ι, z ∈ L ∧ (∀ j, 0 ≤ z j) ∧ 0 < z i

                                                                         
noncomputable def coordinateWitness (L : Submodule ℝ (EVec ι)) (i : ι) : EVec ι := by
  classical
  exact if h : AttainableCoordinate L i then Classical.choose h else 0

theorem coordinateWitness_mem (L : Submodule ℝ (EVec ι)) (i : ι) :
    coordinateWitness L i ∈ L := by
  classical
  by_cases h : AttainableCoordinate L i
  · simpa [coordinateWitness, h] using (Classical.choose_spec h).1
  · simp [coordinateWitness, h]

theorem coordinateWitness_nonneg (L : Submodule ℝ (EVec ι)) (i j : ι) :
    0 ≤ coordinateWitness L i j := by
  classical
  by_cases h : AttainableCoordinate L i
  · simpa [coordinateWitness, h] using (Classical.choose_spec h).2.1 j
  · simp [coordinateWitness, h]

theorem coordinateWitness_pos (L : Submodule ℝ (EVec ι)) {i : ι}
    (h : AttainableCoordinate L i) : 0 < coordinateWitness L i i := by
  classical
  simpa [coordinateWitness, h] using (Classical.choose_spec h).2.2

                                                              
def maximalSupportVector (L : Submodule ℝ (EVec ι)) : EVec ι :=
  ∑ i, coordinateWitness L i

private theorem sum_apply {α : Type*} [Fintype α]
    (v : α → EVec ι) (i : ι) : (∑ a, v a) i = ∑ a, v a i := by
  simpa [PiLp.projₗ] using
    map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : ι ↦ ℝ) i) v Finset.univ

theorem maximalSupportVector_mem (L : Submodule ℝ (EVec ι)) :
    maximalSupportVector L ∈ L := by
  classical
  exact Submodule.sum_mem L fun i _ ↦ coordinateWitness_mem L i

theorem maximalSupportVector_nonneg (L : Submodule ℝ (EVec ι)) (i : ι) :
    0 ≤ maximalSupportVector L i := by
  classical
  rw [maximalSupportVector, sum_apply]
  exact Finset.sum_nonneg fun j _ ↦ coordinateWitness_nonneg L j i

theorem maximalSupportVector_pos_iff (L : Submodule ℝ (EVec ι)) (i : ι) :
    0 < maximalSupportVector L i ↔ AttainableCoordinate L i := by
  classical
  constructor
  · intro hi
    exact ⟨maximalSupportVector L, maximalSupportVector_mem L,
      maximalSupportVector_nonneg L, hi⟩
  · intro hi
    have hle : coordinateWitness L i i ≤ maximalSupportVector L i := by
      rw [maximalSupportVector, sum_apply]
      exact Finset.single_le_sum
        (fun j _ ↦ coordinateWitness_nonneg L j i) (Finset.mem_univ i)
    exact (coordinateWitness_pos L hi).trans_le hle

theorem maximalSupportVector_eq_zero_of_not_attainable
    (L : Submodule ℝ (EVec ι)) {i : ι} (hi : ¬ AttainableCoordinate L i) :
    maximalSupportVector L i = 0 := by
  apply le_antisymm
  · exact le_of_not_gt (fun h ↦ hi ((maximalSupportVector_pos_iff L i).mp h))
  · exact maximalSupportVector_nonneg L i

                                                                                 
noncomputable def inaccessibleSet (L : Submodule ℝ (EVec ι)) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ ¬ AttainableCoordinate L i

@[simp]
theorem mem_inaccessibleSet_iff (L : Submodule ℝ (EVec ι)) (i : ι) :
    i ∈ inaccessibleSet L ↔ ¬ AttainableCoordinate L i := by
  classical
  simp [inaccessibleSet]

                                                       
noncomputable def inaccessibleRestriction (L : Submodule ℝ (EVec ι)) :
    EVec ι →ₗ[ℝ] EVec {i // i ∈ inaccessibleSet L} where
  toFun x := (WithLp.equiv 2 ({i // i ∈ inaccessibleSet L} → ℝ)).symm
    (fun i ↦ x i.1)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

@[simp]
theorem inaccessibleRestriction_apply (L : Submodule ℝ (EVec ι))
    (x : EVec ι) (i : {i // i ∈ inaccessibleSet L}) :
    inaccessibleRestriction L x i = x i.1 :=
  rfl

                                                    
noncomputable def inaccessibleExtension (L : Submodule ℝ (EVec ι)) :
    EVec {i // i ∈ inaccessibleSet L} →ₗ[ℝ] EVec ι where
  toFun y := (WithLp.equiv 2 (ι → ℝ)).symm fun i ↦
    if hi : i ∈ inaccessibleSet L then y ⟨i, hi⟩ else 0
  map_add' x y := by
    ext i
    by_cases hi : i ∈ inaccessibleSet L <;> simp [hi]
  map_smul' a x := by
    ext i
    by_cases hi : i ∈ inaccessibleSet L <;> simp [hi]

@[simp]
theorem inaccessibleExtension_apply_of_mem (L : Submodule ℝ (EVec ι))
    (y : EVec {i // i ∈ inaccessibleSet L}) {i : ι}
    (hi : i ∈ inaccessibleSet L) :
    inaccessibleExtension L y i = y ⟨i, hi⟩ := by
  simp [inaccessibleExtension, hi]

@[simp]
theorem inaccessibleExtension_apply_of_not_mem (L : Submodule ℝ (EVec ι))
    (y : EVec {i // i ∈ inaccessibleSet L}) {i : ι}
    (hi : i ∉ inaccessibleSet L) :
    inaccessibleExtension L y i = 0 := by
  simp [inaccessibleExtension, hi]

                                                                   
noncomputable def projectedInaccessibleSubspace (L : Submodule ℝ (EVec ι)) :
    Submodule ℝ (EVec {i // i ∈ inaccessibleSet L}) :=
  L.map (inaccessibleRestriction L)

theorem inner_inaccessibleExtension_left (L : Submodule ℝ (EVec ι))
    (y : EVec {i // i ∈ inaccessibleSet L}) (x : EVec ι) :
    ⟪inaccessibleExtension L y, x⟫ = ⟪y, inaccessibleRestriction L x⟫ := by
  classical
  simp only [PiLp.inner_apply, inaccessibleExtension, inaccessibleRestriction,
    LinearMap.coe_mk, AddHom.coe_mk, WithLp.equiv_symm_apply, RCLike.inner_apply,
    conj_trivial]
  let g : ι → ℝ := fun i ↦
    if hi : i ∈ inaccessibleSet L then x i * y ⟨i, hi⟩ else 0
  calc
    (∑ i, x i * if hi : i ∈ inaccessibleSet L then y ⟨i, hi⟩ else 0) =
        ∑ i, g i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ inaccessibleSet L
      · simp only [dif_pos hi, g]
      · simp only [dif_neg hi, mul_zero, g]
    _ = ∑ i ∈ inaccessibleSet L, g i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [g, dif_neg hi]
    _ = ∑ i : {i // i ∈ inaccessibleSet L}, g i := by
      exact Finset.sum_subtype (inaccessibleSet L) (fun _ ↦ Iff.rfl) g
    _ = ∑ i : {i // i ∈ inaccessibleSet L}, x i.1 * y i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [g, dif_pos i.2]

                                                                            
                                                           
theorem projectedInaccessibleSubspace_disjoint_simplex
    (L : Submodule ℝ (EVec ι)) [Nonempty {i // i ∈ inaccessibleSet L}] :
    Disjoint (projectedInaccessibleSubspace L :
      Set (EVec {i // i ∈ inaccessibleSet L}))
      (simplex {i // i ∈ inaccessibleSet L}) := by
  classical
  rw [Set.disjoint_left]
  intro v hvS hvSimplex
  rcases hvS with ⟨l, hlL, hlv⟩
  obtain ⟨j, hjpos⟩ := exists_pos_of_mem_simplex hvSimplex
  let x : EVec ι := maximalSupportVector L
  let R : ℝ := ∑ i, |l i| / x i
  have hR_nonneg : 0 ≤ R := by
    exact Finset.sum_nonneg fun i _ ↦
      div_nonneg (abs_nonneg _) (maximalSupportVector_nonneg L i)
  let z : EVec ι := R • x + l
  have hzL : z ∈ L := by
    exact L.add_mem (L.smul_mem R (maximalSupportVector_mem L)) hlL
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    by_cases hi : i ∈ inaccessibleSet L
    · have hnot : ¬ AttainableCoordinate L i := (mem_inaccessibleSet_iff L i).mp hi
      have hxi : x i = 0 := maximalSupportVector_eq_zero_of_not_attainable L hnot
      have hli : l i = v ⟨i, hi⟩ := by
        have happ := congrArg (fun q : EVec {i // i ∈ inaccessibleSet L} ↦ q ⟨i, hi⟩) hlv
        simpa using happ
      simp only [z, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hxi, mul_zero,
        zero_add, hli]
      exact nonneg_of_mem_simplex hvSimplex ⟨i, hi⟩
    · have hatt : AttainableCoordinate L i := by
        simpa [mem_inaccessibleSet_iff] using hi
      have hxi : 0 < x i := (maximalSupportVector_pos_iff L i).mpr hatt
      have hterm : |l i| / x i ≤ R := by
        exact Finset.single_le_sum
          (fun k _ ↦ div_nonneg (abs_nonneg _) (maximalSupportVector_nonneg L k))
          (Finset.mem_univ i)
      have habs : |l i| ≤ R * x i := by
        calc
          |l i| = (|l i| / x i) * x i := (div_mul_cancel₀ _ hxi.ne').symm
          _ ≤ R * x i := mul_le_mul_of_nonneg_right hterm hxi.le
      simp only [z, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      linarith [neg_abs_le (l i)]
  have hzj : 0 < z j.1 := by
    have hnot : ¬ AttainableCoordinate L j.1 :=
      (mem_inaccessibleSet_iff L j.1).mp j.2
    have hxj : x j.1 = 0 := maximalSupportVector_eq_zero_of_not_attainable L hnot
    have hlj : l j.1 = v j := by
      have happ := congrArg (fun q : EVec {i // i ∈ inaccessibleSet L} ↦ q j) hlv
      simpa using happ
    simpa [z, hxj, hlj] using hjpos
  exact ((mem_inaccessibleSet_iff L j.1).mp j.2)
    ⟨z, hzL, hz_nonneg, hzj⟩

   
                                                                 
                                                                      
                                                                          
                
  
theorem subspace_strict_complementarity (L : Submodule ℝ (EVec ι)) :
    ∃ z s : EVec ι,
      z ∈ L ∧ s ∈ Lᗮ ∧
      (∀ i, 0 ≤ z i) ∧ (∀ i, 0 ≤ s i) ∧
      ∀ i, 0 < z i + s i := by
  classical
  let z : EVec ι := maximalSupportVector L
  by_cases hJ : (inaccessibleSet L).Nonempty
  · letI : Nonempty {i // i ∈ inaccessibleSet L} :=
      ⟨⟨Classical.choose hJ, Classical.choose_spec hJ⟩⟩
    let S : Submodule ℝ (EVec {i // i ∈ inaccessibleSet L}) :=
      projectedInaccessibleSubspace L
    have hSclosed : IsClosed (S : Set (EVec {i // i ∈ inaccessibleSet L})) :=
      S.closed_of_finiteDimensional
    have hdisj : Disjoint (S : Set (EVec {i // i ∈ inaccessibleSet L}))
        (simplex {i // i ∈ inaccessibleSet L}) := by
      exact projectedInaccessibleSubspace_disjoint_simplex L
    obtain ⟨f, u, v, hfS, huv, hfSimplex⟩ := geometric_hahn_banach_closed_compact
      S.convex hSclosed simplex_convex simplex_isCompact hdisj
    have hu_pos : 0 < u := by
      simpa using hfS 0 S.zero_mem
    have hv_pos : 0 < v := hu_pos.trans huv
    have hfSzero : ∀ q ∈ S, f q = 0 := by
      intro q hq
      by_contra hn
      let a : ℝ := (u + 1) / f q
      have haq : a • q ∈ S := S.smul_mem a hq
      have hsep := hfS (a • q) haq
      have hfa : f (a • q) = u + 1 := by
        simp only [map_smul, smul_eq_mul, a]
        exact div_mul_cancel₀ (u + 1) hn
      rw [hfa] at hsep
      linarith
    let r : EVec {i // i ∈ inaccessibleSet L} :=
      (InnerProductSpace.toDual ℝ (EVec {i // i ∈ inaccessibleSet L})).symm f
    have hr_eval : ∀ q : EVec {i // i ∈ inaccessibleSet L}, ⟪r, q⟫ = f q := by
      intro q
      exact InnerProductSpace.toDual_symm_apply
    have hr_pos : ∀ j, 0 < r j := by
      intro j
      have hfvert : v < f (simplexVertex j) :=
        hfSimplex (simplexVertex j) (simplexVertex_mem j)
      have hcoord : r j = f (simplexVertex j) := by
        rw [← inner_simplexVertex_right r j]
        exact hr_eval (simplexVertex j)
      rw [hcoord]
      exact hv_pos.trans hfvert
    let s : EVec ι := inaccessibleExtension L r
    have hsOrth : s ∈ Lᗮ := by
      rw [Submodule.mem_orthogonal']
      intro q hqL
      rw [inner_inaccessibleExtension_left]
      rw [hr_eval]
      exact hfSzero _ ⟨q, hqL, rfl⟩
    have hs_nonneg : ∀ i, 0 ≤ s i := by
      intro i
      by_cases hi : i ∈ inaccessibleSet L
      · rw [show s i = r ⟨i, hi⟩ by
          exact inaccessibleExtension_apply_of_mem L r hi]
        exact (hr_pos ⟨i, hi⟩).le
      · rw [show s i = 0 by
          exact inaccessibleExtension_apply_of_not_mem L r hi]
    refine ⟨z, s, maximalSupportVector_mem L, hsOrth,
      maximalSupportVector_nonneg L, hs_nonneg, ?_⟩
    intro i
    by_cases hi : i ∈ inaccessibleSet L
    · have hnot : ¬ AttainableCoordinate L i := (mem_inaccessibleSet_iff L i).mp hi
      have hzi : z i = 0 := maximalSupportVector_eq_zero_of_not_attainable L hnot
      have hsi : s i = r ⟨i, hi⟩ := inaccessibleExtension_apply_of_mem L r hi
      rw [hzi, hsi, zero_add]
      exact hr_pos ⟨i, hi⟩
    · have hatt : AttainableCoordinate L i := by
        by_contra hnot
        exact hi ((mem_inaccessibleSet_iff L i).mpr hnot)
      have hzi : 0 < z i := (maximalSupportVector_pos_iff L i).mpr hatt
      have hsi : s i = 0 := inaccessibleExtension_apply_of_not_mem L r hi
      simpa [hsi] using hzi
  · have hJempty : inaccessibleSet L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    refine ⟨z, 0, maximalSupportVector_mem L, (Lᗮ).zero_mem,
      maximalSupportVector_nonneg L, fun i ↦ by simp, ?_⟩
    intro i
    have hatt : AttainableCoordinate L i := by
      by_contra hnot
      have hi : i ∈ inaccessibleSet L := (mem_inaccessibleSet_iff L i).mpr hnot
      rw [hJempty] at hi
      simp at hi
    simpa using (maximalSupportVector_pos_iff L i).mpr hatt

                                                                     
theorem coordinate_mul_eq_zero_of_nonnegative_orthogonal
    (L : Submodule ℝ (EVec ι)) {z s : EVec ι}
    (hzL : z ∈ L) (hsL : s ∈ Lᗮ)
    (hz : ∀ i, 0 ≤ z i) (hs : ∀ i, 0 ≤ s i) :
    ∀ i, z i * s i = 0 := by
  classical
  have hinner : ⟪s, z⟫ = 0 := (Submodule.mem_orthogonal' L s).mp hsL z hzL
  have hsum : ∑ i, z i * s i = 0 := by
    simpa [PiLp.inner_apply] using hinner
  intro i
  have hle : z i * s i ≤ ∑ j, z j * s j :=
    Finset.single_le_sum (fun j _ ↦ mul_nonneg (hz j) (hs j)) (Finset.mem_univ i)
  rw [hsum] at hle
  nlinarith [mul_nonneg (hz i) (hs i)]

                                      

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]

                                                                               
def blockPair (x y : EVec α) : EVec (Sum α α) :=
  (WithLp.equiv 2 (Sum α α → ℝ)).symm fun a ↦
    match a with
    | Sum.inl i => x i
    | Sum.inr i => y i

@[simp]
theorem blockPair_inl (x y : EVec α) (i : α) : blockPair x y (Sum.inl i) = x i :=
  rfl

@[simp]
theorem blockPair_inr (x y : EVec α) (i : α) : blockPair x y (Sum.inr i) = y i :=
  rfl

                                                     
def leftBlock (q : EVec (Sum α α)) : EVec α :=
  (WithLp.equiv 2 (α → ℝ)).symm fun i ↦ q (Sum.inl i)

                                                      
def rightBlock (q : EVec (Sum α α)) : EVec α :=
  (WithLp.equiv 2 (α → ℝ)).symm fun i ↦ q (Sum.inr i)

@[simp] theorem leftBlock_apply (q : EVec (Sum α α)) (i : α) :
    leftBlock q i = q (Sum.inl i) := rfl

@[simp] theorem rightBlock_apply (q : EVec (Sum α α)) (i : α) :
    rightBlock q i = q (Sum.inr i) := rfl

theorem blockPair_leftBlock_rightBlock (q : EVec (Sum α α)) :
    blockPair (leftBlock q) (rightBlock q) = q := by
  ext a
  rcases a with i | i <;> rfl

theorem inner_blockPair (x y u v : EVec α) :
    ⟪blockPair x y, blockPair u v⟫ = ⟪x, u⟫ + ⟪y, v⟫ := by
  classical
  simp [PiLp.inner_apply, blockPair, Fintype.sum_sum_type]

                                                        
def graphMap (M : PayoffOperator α α) : EVec α →ₗ[ℝ] EVec (Sum α α) where
  toFun x := blockPair x (M x)
  map_add' x y := by
    ext a
    rcases a with i | i <;> simp
  map_smul' a x := by
    ext i
    rcases i with i | i <;> simp

@[simp]
theorem graphMap_apply (M : PayoffOperator α α) (x : EVec α) :
    graphMap M x = blockPair x (M x) := rfl

                                                                    
def graphSubspace (M : PayoffOperator α α) : Submodule ℝ (EVec (Sum α α)) :=
  LinearMap.range (graphMap M)

theorem leftBlock_eq_map_rightBlock_of_mem_graph_orthogonal
    (M : PayoffOperator α α) (hskew : payoffAdjoint M = -M)
    {q : EVec (Sum α α)} (hq : q ∈ (graphSubspace M)ᗮ) :
    leftBlock q = M (rightBlock q) := by
  let d : EVec α := leftBlock q - M (rightBlock q)
  have hgraph : graphMap M d ∈ graphSubspace M := ⟨d, rfl⟩
  have horth : ⟪q, graphMap M d⟫ = 0 :=
    (Submodule.mem_orthogonal' (graphSubspace M) q).mp hq _ hgraph
  rw [← blockPair_leftBlock_rightBlock q, graphMap_apply, inner_blockPair] at horth
  have hright : ⟪rightBlock q, M d⟫ = -⟪M (rightBlock q), d⟫ := by
    calc
      ⟪rightBlock q, M d⟫ = ⟪M d, rightBlock q⟫ := real_inner_comm _ _
      _ = ⟪d, payoffAdjoint M (rightBlock q)⟫ :=
        inner_map_eq_inner_adjoint M d (rightBlock q)
      _ = ⟪d, (-M) (rightBlock q)⟫ := by rw [hskew]
      _ = -⟪d, M (rightBlock q)⟫ := by simp
      _ = -⟪M (rightBlock q), d⟫ := by rw [real_inner_comm]
  rw [hright] at horth
  have hdinner : ⟪d, d⟫ = 0 := by
    change ⟪leftBlock q - M (rightBlock q), d⟫ = 0
    rw [inner_sub_left, sub_eq_add_neg]
    exact horth
  have hnormsq : ‖d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hdinner
  have hnorm : ‖d‖ = 0 := by
    nlinarith [norm_nonneg d]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

   
                                                                      
                                                                            
            
  
theorem skew_strict_complementarity
    (M : PayoffOperator α α) (hskew : payoffAdjoint M = -M) :
    ∃ z : EVec α,
      (∀ a, 0 ≤ z a) ∧
      (∀ a, 0 ≤ M z a) ∧
      (∀ a, z a * M z a = 0) ∧
      ∀ a, 0 < z a + M z a := by
  classical
  obtain ⟨p, s, hpGraph, hsOrth, hpNonneg, hsNonneg, hstrict⟩ :=
    subspace_strict_complementarity (graphSubspace M)
  rcases hpGraph with ⟨u, hu⟩
  have hpEq : p = blockPair u (M u) := hu.symm
  let w : EVec α := rightBlock s
  have hsLeft : leftBlock s = M w := by
    exact leftBlock_eq_map_rightBlock_of_mem_graph_orthogonal M hskew hsOrth
  let z : EVec α := u + w
  have huNonneg : ∀ a, 0 ≤ u a := by
    intro a
    simpa [hpEq] using hpNonneg (Sum.inl a)
  have hMuNonneg : ∀ a, 0 ≤ M u a := by
    intro a
    simpa [hpEq] using hpNonneg (Sum.inr a)
  have hwNonneg : ∀ a, 0 ≤ w a := by
    intro a
    exact hsNonneg (Sum.inr a)
  have hMwNonneg : ∀ a, 0 ≤ M w a := by
    intro a
    rw [← hsLeft]
    exact hsNonneg (Sum.inl a)
  have hzNonneg : ∀ a, 0 ≤ z a := by
    intro a
    simp only [z, PiLp.add_apply]
    exact add_nonneg (huNonneg a) (hwNonneg a)
  have hMzNonneg : ∀ a, 0 ≤ M z a := by
    intro a
    simp only [z, map_add, PiLp.add_apply]
    exact add_nonneg (hMuNonneg a) (hMwNonneg a)
  have hzMzPos : ∀ a, 0 < z a + M z a := by
    intro a
    have hleft := hstrict (Sum.inl a)
    have hright := hstrict (Sum.inr a)
    have hsLeftApply : s (Sum.inl a) = M w a := by
      rw [← hsLeft]
      rfl
    have hsRightApply : s (Sum.inr a) = w a := rfl
    simp only [hpEq, blockPair_inl, blockPair_inr, hsLeftApply] at hleft
    simp only [hpEq, blockPair_inl, blockPair_inr, hsRightApply] at hright
    simp only [z, PiLp.add_apply, map_add]
    nlinarith
  have hinner : ⟪z, M z⟫ = 0 := by
    have hadj := inner_map_eq_inner_adjoint M z z
    rw [hskew] at hadj
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right] at hadj
    rw [real_inner_comm] at hadj
    linarith
  have hsum : ∑ a, z a * M z a = 0 := by
    simpa [PiLp.inner_apply, mul_comm] using hinner
  have hproducts : ∀ a, z a * M z a = 0 := by
    intro a
    have hle : z a * M z a ≤ ∑ b, z b * M z b :=
      Finset.single_le_sum
        (fun b _ ↦ mul_nonneg (hzNonneg b) (hMzNonneg b)) (Finset.mem_univ a)
    rw [hsum] at hle
    exact le_antisymm hle (mul_nonneg (hzNonneg a) (hMzNonneg a))
  exact ⟨z, hzNonneg, hMzNonneg, hproducts, hzMzPos⟩

end

end AltGDA
