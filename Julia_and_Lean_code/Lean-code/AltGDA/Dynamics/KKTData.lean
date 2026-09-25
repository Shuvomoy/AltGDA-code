import AltGDA.Dynamics.AltGDA
import AltGDA.Simplex.KKT

   
                                           

                                                                          
                                                                               
                                                        
  

open scoped BigOperators RealInnerProductSpace

namespace AltGDA

noncomputable section

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

def xProjectionInput (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : EVec ι :=
  xIter A η s0 t + η • vField A η s0 t

def yProjectionInput (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : EVec κ :=
  yIter A η s0 t + η • uField A η s0 t

def gammaKKT (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  simplexProjectionThreshold (xProjectionInput A η s0 t) / η

def lambdaKKT (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : ℝ :=
  simplexProjectionThreshold (yProjectionInput A η s0 t) / η

def muKKT (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : EVec ι :=
  η⁻¹ • simplexProjectionMultiplier (xProjectionInput A η s0 t)

def rhoKKT (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) : EVec κ :=
  η⁻¹ • simplexProjectionMultiplier (yProjectionInput A η s0 t)

theorem xIter_succ_eq_projectionInput (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    xIter A η s0 (t + 1) = simplexProj (xProjectionInput A η s0 t) := by
  simpa [xProjectionInput] using xIter_succ_eq_projection A η s0 t

theorem yIter_succ_eq_projectionInput (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) :
    yIter A η s0 (t + 1) = simplexProj (yProjectionInput A η s0 t) := by
  simpa [yProjectionInput] using yIter_succ_eq_projection A η s0 t

theorem muKKT_nonneg (A : PayoffOperator ι κ) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) (i : ι) :
    0 ≤ muKKT A η s0 t i := by
  simp only [muKKT, PiLp.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hη.le)
    (simplexProjectionMultiplier_nonneg _ i)

theorem rhoKKT_nonneg (A : PayoffOperator ι κ) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) (j : κ) :
    0 ≤ rhoKKT A η s0 t j := by
  simp only [rhoKKT, PiLp.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hη.le)
    (simplexProjectionMultiplier_nonneg _ j)

theorem muKKT_complementarity (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) (i : ι) :
    muKKT A η s0 t i * xIter A η s0 (t + 1) i = 0 := by
  rw [xIter_succ_eq_projectionInput]
  change η⁻¹ * simplexProjectionMultiplier (xProjectionInput A η s0 t) i *
      simplexProj (xProjectionInput A η s0 t) i = 0
  rw [mul_assoc, simplexProjection_complementarity, mul_zero]

theorem rhoKKT_complementarity (A : PayoffOperator ι κ) (η : ℝ)
    (s0 : GameState ι κ) (t : ℕ) (j : κ) :
    rhoKKT A η s0 t j * yIter A η s0 (t + 1) j = 0 := by
  rw [yIter_succ_eq_projectionInput]
  change η⁻¹ * simplexProjectionMultiplier (yProjectionInput A η s0 t) j *
      simplexProj (yProjectionInput A η s0 t) j = 0
  rw [mul_assoc, simplexProjection_complementarity, mul_zero]

theorem deltaX_kkt (A : PayoffOperator ι κ) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    deltaX A η s0 t = η •
      (vField A η s0 t - gammaKKT A η s0 t • ones ι + muKKT A η s0 t) := by
  apply PiLp.ext
  intro i
  have hstat := simplexProjection_stationarity (xProjectionInput A η s0 t)
  have hnext := xIter_succ_eq_projectionInput A η s0 t
  have hcoord := congrArg (fun z : EVec ι ↦ z i) (hnext.trans hstat)
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, ones_apply,
    smul_eq_mul] at hcoord ⊢
  simp only [deltaX, xProjectionInput, gammaKKT, muKKT, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hcoord ⊢
  field_simp [ne_of_gt hη] at hcoord ⊢
  linarith

theorem deltaY_kkt (A : PayoffOperator ι κ) {η : ℝ} (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    deltaY A η s0 t = η •
      (uField A η s0 t - lambdaKKT A η s0 t • ones κ + rhoKKT A η s0 t) := by
  apply PiLp.ext
  intro j
  have hstat := simplexProjection_stationarity (yProjectionInput A η s0 t)
  have hnext := yIter_succ_eq_projectionInput A η s0 t
  have hcoord := congrArg (fun z : EVec κ ↦ z j) (hnext.trans hstat)
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, ones_apply,
    smul_eq_mul] at hcoord ⊢
  simp only [deltaY, yProjectionInput, lambdaKKT, rhoKKT, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hcoord ⊢
  field_simp [ne_of_gt hη] at hcoord ⊢
  linarith

theorem deltaX_norm_le (A : PayoffOperator ι κ) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    ‖deltaX A η s0 t‖ ≤ η * L := by
  have hnonexp := simplexProj_nonexpansive
    (xProjectionInput A η s0 t) (xIter A η s0 t)
  rw [simplexProj_fixed (xIter_mem A η s0 t)] at hnonexp
  have hv : ‖vField A η s0 t‖ ≤ L := by
    calc
      ‖vField A η s0 t‖ = ‖payoffAdjoint A (yIter A η s0 t)‖ := by
        simp [vField]
      _ ≤ L * ‖yIter A η s0 t‖ :=
        norm_adjoint_map_le_of_opNorm_le A hA _
      _ ≤ L := by
        simpa using mul_le_mul_of_nonneg_left
          (simplex_norm_le_one (yIter_mem A η s0 t)) hL
  rw [← xIter_succ_eq_projectionInput, ← deltaX] at hnonexp
  calc
    ‖deltaX A η s0 t‖ ≤ ‖xProjectionInput A η s0 t - xIter A η s0 t‖ := hnonexp
    _ = η * ‖vField A η s0 t‖ := by
      simp [xProjectionInput, norm_smul, abs_of_pos hη]
    _ ≤ η * L := mul_le_mul_of_nonneg_left hv hη.le

theorem deltaY_norm_le (A : PayoffOperator ι κ) {L η : ℝ}
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) (hη : 0 < η)
    (s0 : GameState ι κ) (t : ℕ) :
    ‖deltaY A η s0 t‖ ≤ η * L := by
  have hnonexp := simplexProj_nonexpansive
    (yProjectionInput A η s0 t) (yIter A η s0 t)
  rw [simplexProj_fixed (yIter_mem A η s0 t)] at hnonexp
  have hu : ‖uField A η s0 t‖ ≤ L := by
    calc
      ‖uField A η s0 t‖ ≤ L * ‖xIter A η s0 (t + 1)‖ := by
        exact norm_map_le_of_opNorm_le A hA _
      _ ≤ L := by
        simpa using mul_le_mul_of_nonneg_left
          (simplex_norm_le_one (xIter_mem A η s0 (t + 1))) hL
  rw [← yIter_succ_eq_projectionInput, ← deltaY] at hnonexp
  calc
    ‖deltaY A η s0 t‖ ≤ ‖yProjectionInput A η s0 t - yIter A η s0 t‖ := hnonexp
    _ = η * ‖uField A η s0 t‖ := by
      simp [yProjectionInput, norm_smul, abs_of_pos hη]
    _ ≤ η * L := mul_le_mul_of_nonneg_left hu hη.le

end


end AltGDA
