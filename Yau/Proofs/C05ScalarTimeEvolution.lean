import Yau.Proofs.C05MetricTimeDerivative
import Yau.Proofs.C05RicciTimeDerivative

/-! Differentiate the actual inverse-metric/Ricci trace. This proves the
scalar evolution equation from the original flow, without an evolution axiom. -/

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}

def ricciNormSq (k : HermitianField M) (x : M.Carrier) : ℝ :=
  traceWith (gMat k x) (ricci k x * (gMat k x)⁻¹ * ricci k x)

theorem scalar_hasDerivAt_laplacian_add_ricciNormSq (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => scalarCurvature (h s) x)
      (laplacian (h t) (scalarCurvature (h t)) x + ricciNormSq (h t) x) t := by
  have hp := hasDerivAt_complex_trace_mul
    (gMat_inverse_hasDerivAt o h U P ρ hf x ht)
    (ricci_hasDerivAt_scalar_levi o h U P ρ hf x ht)
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  change HasDerivAt (fun s => scalarCurvature (h s) x)
    ((((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) * ricci (h t) x +
      (gMat (h t) x)⁻¹ * levi (scalarCurvature (h t)) x).trace.re) t at hd
  convert hd using 1
  simp only [laplacian, ricciNormSq, traceWith, Matrix.trace_add, Complex.add_re,
    Matrix.mul_assoc]
  ring

theorem scalar_time_evolution (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => scalarCurvature (h s) x) t =
      laplacian (h t) (scalarCurvature (h t)) x + ricciNormSq (h t) x :=
  (scalar_hasDerivAt_laplacian_add_ricciNormSq o h U P ρ hf x ht).deriv

end Yau.Proofs.C05Aux
