import Yau.Proofs.V04HermitianCalculus
import Yau.Proofs.V04ScalarMajorant

/-! The scalar estimates are transported to the actual frozen spectral
expression, retaining its matrix order and the fixed smoothing parameter. -/

open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem smoothMajorant_eq_cfc (δ : ℝ) (A : CotangentMatrix n) (hA : A.IsHermitian) :
    smoothMajorant δ A = cfc (scalarMajorant δ) A :=
  hermitianScalar_eq_cfc _ A hA

private theorem cfc_real_const (δ : ℝ) (A : CotangentMatrix n) (hA : A.IsHermitian) :
    cfc (fun _ : ℝ => δ) A = (δ : ℂ) • (1 : CotangentMatrix n) := by
  rw [cfc_const δ A (show IsSelfAdjoint A from hA)]
  ext i j
  simp [Algebra.algebraMap_eq_smul_one]

theorem smoothMajorant_ge_delta {δ : ℝ} (hδ : 0 < δ) (A : CotangentMatrix n)
    (hA : A.IsHermitian) :
    (smoothMajorant δ A - (δ : ℂ) • (1 : CotangentMatrix n)).PosSemidef := by
  have hm := cfc_mono (a := A) (f := fun _ : ℝ => δ) (g := scalarMajorant δ)
    (fun x _ => (scalarMajorant_bounds hδ x).1)
    continuousOn_const (scalarMajorant_contDiff hδ).continuous.continuousOn
  rw [cfc_real_const δ A hA, ← smoothMajorant_eq_cfc δ A hA] at hm
  exact Matrix.le_iff.mp hm

theorem smoothMajorant_ge_matrix_add_delta {δ : ℝ} (hδ : 0 < δ)
    (A : CotangentMatrix n) (hA : A.IsHermitian) :
    (smoothMajorant δ A - (A + (δ : ℂ) • (1 : CotangentMatrix n))).PosSemidef := by
  have hm := cfc_mono (a := A) (f := fun x : ℝ => x + δ) (g := scalarMajorant δ)
    (fun x _ => (scalarMajorant_bounds hδ x).2.1)
    (by fun_prop) (scalarMajorant_contDiff hδ).continuous.continuousOn
  rw [cfc_add A (fun x : ℝ => x) (fun _ => δ) continuousOn_id continuousOn_const,
    cfc_id' (R := ℝ) A (show IsSelfAdjoint A from hA),
    cfc_real_const δ A hA, ← smoothMajorant_eq_cfc δ A hA] at hm
  exact Matrix.le_iff.mp hm

theorem smoothMajorant_sub_positive_posSemidef {δ : ℝ} (hδ : 0 < δ)
    (A : CotangentMatrix n) (hA : A.IsHermitian) :
    (smoothMajorant δ A - matrixPositive A).PosSemidef := by
  have hm := cfc_mono (a := A) (f := fun x : ℝ => max x 0) (g := scalarMajorant δ)
    (fun x _ => by linarith [(scalarMajorant_bounds hδ x).2.2.1])
    (by fun_prop) (scalarMajorant_contDiff hδ).continuous.continuousOn
  rw [← hermitianScalar_eq_cfc (fun x : ℝ => max x 0) A hA,
    ← smoothMajorant_eq_cfc δ A hA] at hm
  exact Matrix.le_iff.mp hm

theorem smoothMajorant_sub_positive_le {δ : ℝ} (hδ : 0 < δ)
    (A : CotangentMatrix n) (hA : A.IsHermitian) :
    (((3 * δ / 2 : ℝ) : ℂ) • (1 : CotangentMatrix n) -
      (smoothMajorant δ A - matrixPositive A)).PosSemidef := by
  have hm := cfc_mono (a := A) (f := scalarMajorant δ)
    (g := fun x : ℝ => max x 0 + 3 * δ / 2)
    (fun x _ => by linarith [(scalarMajorant_bounds hδ x).2.2.2])
    (scalarMajorant_contDiff hδ).continuous.continuousOn (by fun_prop)
  rw [cfc_add A (fun x : ℝ => max x 0) (fun _ => 3 * δ / 2) (by fun_prop) continuousOn_const,
    ← hermitianScalar_eq_cfc (fun x : ℝ => max x 0) A hA,
    cfc_real_const (3 * δ / 2) A hA, ← smoothMajorant_eq_cfc δ A hA] at hm
  have hp := Matrix.le_iff.mp hm
  change (matrixPositive A + ((3 * δ / 2 : ℝ) : ℂ) • 1 - smoothMajorant δ A).PosSemidef at hp
  convert hp using 1 <;> abel

end Yau.Blueprint.V04Proof
