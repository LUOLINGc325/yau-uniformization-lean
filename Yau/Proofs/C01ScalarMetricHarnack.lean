import Yau.Proofs.C01RicciTraceBound
import Yau.Proofs.C01ScalarHarnack
import Yau.Proofs.C01RicciNonnegative

/-! The original scalar differential inequality in the metric form
that integrates even when the scalar curvature vanishes. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_metric_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (V : ComplexVector n) :
    0 ≤ deriv (fun s => scalarCurvature (h s) x) t + t⁻¹ * scalarCurvature (h t) x +
      2 * (∑ i, V i * wirt (fun z => Complex.ofReal (inChart x (scalarCurvature (h t)) z))
        (chartPt x x) (stdVec i)).re +
      scalarCurvature (h t) x *
        (star (WithLp.ofLp V) ⬝ᵥ (gMat (h t) x *ᵥ WithLp.ofLp V)).re := by
  have hb := quadratic_le_traceWith_mul_metric (gMat (h t) x) (ricci (h t) x)
    (Alignment.Y03Proof.hMat_posDef (h t) x (chartPt x x)
      (mem_extChartAt_target (I := ComplexModel n) x))
    (localizedFlow_ricci_posSemidef_posTime hflow hjoint x ht) (WithLp.ofLp V)
  have hh := localizedFlow_scalar_harnack hflow hjoint x ht V
  change (star (WithLp.ofLp V) ⬝ᵥ (ricci (h t) x *ᵥ WithLp.ofLp V)).re ≤
    scalarCurvature (h t) x *
      (star (WithLp.ofLp V) ⬝ᵥ (gMat (h t) x *ᵥ WithLp.ofLp V)).re at hb
  linarith

end Yau.NodeProofs.C01Aux
