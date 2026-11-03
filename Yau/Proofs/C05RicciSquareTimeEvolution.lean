import Yau.Proofs.C05ComplexMatrixProductDerivative
import Yau.Proofs.C05ScalarTimeEvolution
import Yau.Proofs.C05LaplacianTimeDerivative

/-! The inverse-metric variation supplies both cubic Ricci terms in the
time derivative of the actual squared Ricci norm. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}

def ricciCube (k : HermitianField M) (x : M.Carrier) : ℝ :=
  (((gMat k x)⁻¹ * ricci k x) * ((gMat k x)⁻¹ * ricci k x) *
    ((gMat k x)⁻¹ * ricci k x)).trace.re

set_option backward.isDefEq.respectTransparency false in
theorem ricciNormSq_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ricciNormSq (h s) x)
      (2 * ricciLeviPairing (h t) (scalarCurvature (h t)) x + 2 * ricciCube (h t) x) t := by
  let B (s : ℝ) := (gMat (h s) x)⁻¹ * ricci (h s) x
  let C := (gMat (h t) x)⁻¹ * levi (scalarCurvature (h t)) x
  let D := ((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) * ricci (h t) x + C
  have hB : ∀ i j, HasDerivAt (fun s => B s i j) (D i j) t :=
    hasDerivAt_complex_matrix_mul
      (gMat_inverse_hasDerivAt o h U P ρ hf x ht)
      (ricci_hasDerivAt_scalar_levi o h U P ρ hf x ht)
  have hp := hasDerivAt_complex_trace_mul hB hB
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  have hD : D = B t * B t + C := by simp only [D, B, Matrix.mul_assoc]
  have he : (D * B t + B t * D).trace =
      2 * (B t * B t * B t).trace + 2 * (B t * C).trace := by
    rw [hD, Matrix.add_mul, Matrix.mul_add]
    simp only [Matrix.trace_add]
    rw [Matrix.trace_mul_comm C (B t)]
    simp only [Matrix.mul_assoc]
    ring
  change HasDerivAt (fun s => (B s * B s).trace.re) (D * B t + B t * D).trace.re t at hd
  rw [he] at hd
  convert hd using 1
  · funext s
    simp only [ricciNormSq, traceWith, B, Matrix.mul_assoc]
  · simp only [ricciLeviPairing, ricciCube, traceWith, B, C, Matrix.mul_assoc,
      Complex.add_re, Complex.mul_re]
    norm_num
    ring

end Yau.Proofs.C05Aux
