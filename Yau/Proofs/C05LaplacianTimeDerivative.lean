import Yau.Proofs.C05SpaceTimeDerivative
import Yau.Proofs.C05MetricTimeDerivative

/-! The time derivative of the actual complex Laplacian includes the genuine
inverse-metric variation. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}

def ricciLeviPairing (k : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  traceWith (gMat k x) (ricci k x * (gMat k x)⁻¹ * levi f x)

theorem laplacian_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : STF X)
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => laplacian (h s) (fun y => u y s) x)
      (laplacian (h t) (fun y => timeDeriv u y t) x +
        ricciLeviPairing (h t) (fun y => u y t) x) t := by
  have hp := hasDerivAt_complex_trace_mul
    (gMat_inverse_hasDerivAt o h U P ρ hf x ht)
    (hasDerivAt_levi_of_smoothSpaceTime isOpen_Ioi hu x ht)
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  change HasDerivAt (fun s => laplacian (h s) (fun y => u y s) x)
    ((((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) * levi (fun y => u y t) x +
      (gMat (h t) x)⁻¹ * levi (fun y => timeDeriv u y t) x).trace.re) t at hd
  convert hd using 1
  simp only [laplacian, ricciLeviPairing, traceWith, Matrix.trace_add, Complex.add_re,
    Matrix.mul_assoc]
  ring

end Yau.Proofs.C05Aux
