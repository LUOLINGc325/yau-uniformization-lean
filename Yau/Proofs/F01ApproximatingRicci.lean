import Yau.Proofs.F01ControlledConformalBounds
import Yau.Proofs.F01ConformalRicci

/-! The Chern Ricci form of the actual approximation, with the original
ambient Ricci tensor transported through the open inclusion. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem openRestrictedField_ricci (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))
    (g : HermitianField M) (a : (openConnectedManifold M S hS).Carrier) :
    ricci (openRestrictedField M S hS g) a = ricci g a.val := by
  have he : logDet (openRestrictedField M S hS g) a =ᶠ[𝓝 (chartPt a a)] logDet g a.val := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
      (mem_extChartAt_target a)] with z hz
    unfold logDet
    rw [openRestrictedField_hMat M S hS g a hz]
  unfold ricci
  rw [LeafProofs.L22Aux.leviC_congr_of_eventuallyEq he]
  rfl

theorem approximatingScalar_smoothFn (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (o : M.Carrier) {L : ℝ} (hL : 0 < L) (ho : u o < L) :
    SmoothFn (approximatingScalar M u hu o L ho) := by
  apply conformalScalar_smoothFn_openRestriction M (sublevelOpens M u hu o L)
    (sublevelComponent_isConnected ho) hu hL
  intro x hx
  exact sublevelComponent_subset u o L hx

theorem approximatingMetric_ricci (g : HermitianField M) (hg : MetricSmooth g)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (o : M.Carrier)
    {L : ℝ} (hL : 0 < L) (ho : u o < L)
    (x : (sublevelManifold M u hu o L ho).Carrier) :
    ricci (approximatingMetric M g u hu o L ho) x =
      ricci g x.val - (n : ℂ) • levi (approximatingScalar M u hu o L ho) x := by
  let g0 := approximatingBaseMetric M g u hu o L ho
  have hg0 : MetricSmooth g0 := openRestrictedField_metricSmooth M
    (sublevelOpens M u hu o L) (sublevelComponent_isConnected ho) hg
  have hf := approximatingScalar_smoothFn u hu o hL ho
  have hr := conformalField_ricci g0 hg0 (approximatingScalar M u hu o L ho) hf x
  have hb : ricci g0 x = ricci g x.val :=
    openRestrictedField_ricci (sublevelOpens M u hu o L) (sublevelComponent_isConnected ho) g x
  rw [hb] at hr
  exact hr

end Yau.NodeProofs.F01Aux
