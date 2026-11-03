import Yau.Proofs.P06ClipFunctions
import Yau.Proofs.P06MatrixHilbertSchmidt

noncomputable section
open scoped ComplexOrder MatrixOrder ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux.Clip

def matrixIntervalClip {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) := cfc (intervalClip C) A
def matrixUpperResidual {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :=
  cfc (fun r : ℝ => max (r - C) 0) A
def matrixLowerResidual {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :=
  cfc (fun r : ℝ => max (-r - C) 0) A

theorem matrix_cfc_const {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    cfc (fun _ : ℝ => C) A = C • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [cfc_const C A (show IsSelfAdjoint A from hA), Algebra.algebraMap_eq_smul_one]

theorem matrixIntervalClip_hermitian {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (matrixIntervalClip C A).IsHermitian := IsSelfAdjoint.cfc

theorem matrixIntervalClip_bounds {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (C • (1 : Matrix (Fin n) (Fin n) ℂ) - matrixIntervalClip C A).PosSemidef ∧
      (matrixIntervalClip C A + C • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have hf := (intervalClip_lipschitz C).continuous
  have hu : 0 ≤ cfc (fun r : ℝ => C - intervalClip C r) A :=
    cfc_nonneg (fun r _ => sub_nonneg.mpr (intervalClip_mem hC r).2)
  have hl : 0 ≤ cfc (fun r : ℝ => intervalClip C r + C) A :=
    cfc_nonneg (fun r _ => by linarith [(intervalClip_mem hC r).1])
  rw [cfc_sub (a := A) (f := fun _ : ℝ => C) (g := intervalClip C)
    continuous_const.continuousOn hf.continuousOn, matrix_cfc_const C A hA] at hu
  rw [cfc_add (a := A) (f := intervalClip C) (g := fun _ : ℝ => C)
    hf.continuousOn continuous_const.continuousOn, matrix_cfc_const C A hA] at hl
  exact ⟨Matrix.nonneg_iff_posSemidef.mp hu, Matrix.nonneg_iff_posSemidef.mp hl⟩

theorem matrixIntervalClip_residual_positive {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (matrixUpperResidual C A).PosSemidef ∧ (matrixLowerResidual C A).PosSemidef := by
  constructor
  · exact Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg (fun r _ => le_max_right (r - C) 0))
  · exact Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg (fun r _ => le_max_right (-r - C) 0))

theorem matrixIntervalClip_residual {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    A - matrixIntervalClip C A = matrixUpperResidual C A - matrixLowerResidual C A := by
  have hf := (intervalClip_lipschitz C).continuous
  have hu : Continuous (fun r : ℝ => max (r - C) 0) := by fun_prop
  have hl : Continuous (fun r : ℝ => max (-r - C) 0) := by fun_prop
  calc
    _ = cfc (fun r : ℝ => r - intervalClip C r) A := by
      rw [cfc_sub (a := A) (f := fun r : ℝ => r) (g := intervalClip C) continuous_id.continuousOn hf.continuousOn,
        cfc_id' ℝ A (show IsSelfAdjoint A from hA)]
      rfl
    _ = cfc (fun r : ℝ => max (r - C) 0 - max (-r - C) 0) A :=
      cfc_congr (fun r _ => intervalClip_residual hC r)
    _ = _ := by
      rw [cfc_sub (a := A) (f := fun r : ℝ => max (r - C) 0) (g := fun r : ℝ => max (-r - C) 0)
        hu.continuousOn hl.continuousOn]
      rfl

theorem matrixIntervalClip_upper_orthogonal {n : ℕ} (C : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    matrixUpperResidual C A * (C • (1 : Matrix (Fin n) (Fin n) ℂ) - matrixIntervalClip C A) = 0 := by
  have hf := (intervalClip_lipschitz C).continuous
  have hu : Continuous (fun r : ℝ => max (r - C) 0) := by fun_prop
  have hd : C • (1 : Matrix (Fin n) (Fin n) ℂ) - matrixIntervalClip C A =
      cfc (fun r : ℝ => C - intervalClip C r) A := by
    rw [cfc_sub (a := A) (f := fun _ : ℝ => C) (g := intervalClip C)
      continuous_const.continuousOn hf.continuousOn, matrix_cfc_const C A hA]
    rfl
  change cfc (fun r : ℝ => max (r - C) 0) A * _ = 0
  rw [hd, ← cfc_mul (a := A) (f := fun r : ℝ => max (r - C) 0)
      (g := fun r : ℝ => C - intervalClip C r) hu.continuousOn (continuous_const.sub hf).continuousOn,
    ← cfc_zero ℝ A]
  exact cfc_congr (fun r _ => intervalClip_upper_orthogonal C r)

theorem matrixIntervalClip_lower_orthogonal {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    matrixLowerResidual C A * (matrixIntervalClip C A + C • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  have hf := (intervalClip_lipschitz C).continuous
  have hl : Continuous (fun r : ℝ => max (-r - C) 0) := by fun_prop
  have hd : matrixIntervalClip C A + C • (1 : Matrix (Fin n) (Fin n) ℂ) =
      cfc (fun r : ℝ => intervalClip C r + C) A := by
    rw [cfc_add (a := A) (f := intervalClip C) (g := fun _ : ℝ => C)
      hf.continuousOn continuous_const.continuousOn, matrix_cfc_const C A hA]
    rfl
  change cfc (fun r : ℝ => max (-r - C) 0) A * _ = 0
  rw [hd, ← cfc_mul (a := A) (f := fun r : ℝ => max (-r - C) 0)
      (g := fun r : ℝ => intervalClip C r + C) hl.continuousOn (hf.add continuous_const).continuousOn,
    ← cfc_zero ℝ A]
  exact cfc_congr (fun r _ => intervalClip_lower_orthogonal hC r)

end Yau.NodeProofs.P06Aux.Clip
