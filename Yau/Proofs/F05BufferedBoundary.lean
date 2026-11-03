import Yau.Proofs.F05BoundaryCharts
import Yau.Proofs.F05BufferedChart

/-! The genuine physical boundary chart has a fixed radius-four target buffer. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.HeatConcreteBindings Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothPrecompact_buffered_boundary_chart {O : Set M.Carrier}
    (hO : SmoothPrecompactDomain O) {p : M.Carrier} (hp : p ∈ frontier O) :
    ∃ (x : M.Carrier) (j : RIdx n) (c : OpenPartialHomeomorph (Space n) (Space n)),
      p ∈ (extChartAt (ComplexModel n) x).source ∧ chartPt x p ∈ c.source ∧
      c (chartPt x p) = 0 ∧ c.source ⊆ chartTarget x ∧ Metric.closedBall 0 4 ⊆ c.target ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target ∧
      ∀ z ∈ c.source,
        (chartInv x z ∈ O ↔ realCoord (c z) j < 0) ∧
        (chartInv x z ∈ closure O ↔ realCoord (c z) j ≤ 0) ∧
        (chartInv x z ∈ frontier O ↔ realCoord (c z) j = 0) := by
  obtain ⟨x,j,c₀,hpx,hpc,hcp,hcV,hc₀,hci₀,hfaces⟩ := smoothPrecompact_boundary_chart hO hp
  obtain ⟨q,c,hq,hsource,hbuffer,hcenter,hforward,hinverse,hc,hci⟩ :=
    buffered_smooth_chart c₀ hpc hcp hc₀ hci₀
  refine ⟨x,j,c,hpx,by rwa [hsource],hcenter,by rwa [hsource],hbuffer,hc,hci,?_⟩
  intro z hz
  obtain ⟨hO,hK,hF⟩ := hfaces z (by rwa [← hsource])
  have hcoord : realCoord (c z) j = q⁻¹ * realCoord (c₀ z) j := by
    rw [hforward z, ← realCoordLinear_apply, map_smul, smul_eq_mul, realCoordLinear_apply]
  have hlt : q⁻¹ * realCoord (c₀ z) j < 0 ↔ realCoord (c₀ z) j < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ (inv_pos.mpr hq) :
      q⁻¹ * realCoord (c₀ z) j < q⁻¹ * 0 ↔ realCoord (c₀ z) j < 0)
  have hle : q⁻¹ * realCoord (c₀ z) j ≤ 0 ↔ realCoord (c₀ z) j ≤ 0 := by
    simpa only [mul_zero] using (mul_le_mul_iff_right₀ (inv_pos.mpr hq) :
      q⁻¹ * realCoord (c₀ z) j ≤ q⁻¹ * 0 ↔ realCoord (c₀ z) j ≤ 0)
  rw [hcoord]
  refine ⟨hO.trans hlt.symm,hK.trans hle.symm,?_⟩
  simpa only [mul_eq_zero,inv_ne_zero hq.ne',false_or] using hF

end Yau.Proofs.F05Aux
