import Yau.Proofs.E02EnvelopeBounds
import Yau.Proofs.E02ChartGap
import Yau.Proofs.E02HermitianQuadratic

open Matrix Set
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Feasibility for the ORIGINAL envelope and the actual constant-disc
upper bound give B ≤ h^{-T} in the fixed original chart. -/
theorem feasibleEllipsoid_le_chartCometric {n : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x z t B) :
    (chartCometric X h x z t-B).PosSemidef := by
  apply (hermitian_posSemidef_iff_re_quadratic_nonneg _
    ((chartCometric_posDef X h x z t hz).isHermitian.sub hB.1.isHermitian)).mpr
  intro v
  let η : ComplexVector n := WithLp.toLp 2 v
  have hDom : (z,η,t) ∈ envelopeDomain X T x := ⟨hz,ht⟩
  have hLower := hB.2 η
  have hUpper := (envelopeChart_bounds X h T x (z,η,t) hDom).2
  have hScalar := EReal.coe_le_coe_iff.mp (hLower.trans hUpper)
  rw [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re]
  exact sub_nonneg.mpr hScalar

end Yau.NodeProofs.E02Aux
