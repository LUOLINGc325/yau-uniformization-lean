import Yau.Proofs.F01ApproximatingRicci
import Yau.Proofs.F01LaplacianLinearity

/-! On the actual interior core the chosen conformal profile vanishes
on a neighborhood, not merely at the point. Its native Levi tensor is zero. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem conformalScalar_chart_eventually_zero (u : M.Carrier → ℝ) (hu : SmoothFn u)
    {L : ℝ} (_hL : 0 < L) (x : M.Carrier) (hx : u x / L < 1 / 2) :
    inChart x (conformalScalar u L) =ᶠ[𝓝 (chartPt x x)] (fun _ => 0) := by
  have hux : inChart x u (chartPt x x) = u x := by simp [inChart, chartInv, chartPt]
  have hc : ContinuousAt (fun z => inChart x u z / L) (chartPt x x) :=
    (smoothFn_chart_contDiffAt hu x).continuousAt.div_const L
  have hsmall : ∀ᶠ z in 𝓝 (chartPt x x), inChart x u z / L < 1 / 2 := by
    apply hc (Iio_mem_nhds ?_)
    simpa only [hux] using hx
  filter_upwards [hsmall] with z hz
  exact conformalProfile_zero hz.le

theorem conformalScalar_levi_zero_on_core (u : M.Carrier → ℝ) (hu : SmoothFn u)
    {L : ℝ} (hL : 0 < L) (x : M.Carrier) (hx : u x / L < 1 / 2) :
    levi (conformalScalar u L) x = 0 := by
  change leviC (inChart x (conformalScalar u L)) (chartPt x x) = _
  rw [LeafProofs.L22Aux.leviC_congr_of_eventuallyEq
    (conformalScalar_chart_eventually_zero u hu hL x hx)]
  exact LeafProofs.L17Aux.leviC_const 0 (chartPt x x)

theorem approximatingScalar_levi_zero_on_core (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (o : M.Carrier) {L : ℝ} (hL : 0 < L) (ho : u o < L)
    (x : (sublevelManifold M u hu o L ho).Carrier) (hx : u x.val / L < 1 / 2) :
    levi (approximatingScalar M u hu o L ho) x = 0 := by
  exact conformalScalar_levi_zero_on_core
    (fun y : (sublevelManifold M u hu o L ho).Carrier => u y.val)
    (smoothFn_openRestriction M (sublevelOpens M u hu o L)
      (sublevelComponent_isConnected ho) hu) hL x hx

end Yau.NodeProofs.F01Aux
