import Yau.Proofs.D02PotentialCompactness
import Yau.LeafProofs.L08

/-! Actual smooth real planar potentials and their nonnegative ordinary
Laplacians, with the exact L08 normalization. -/

open scoped Manifold Topology ContDiff ComplexOrder
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

theorem smoothFn_disc_contDiffAt {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : ContDiffAt ℝ ∞ (fun w => u (f w)) z := by
  let y := f z
  let T : ℂ → ComplexVector n := fun w => chartPt y (f w)
  have hT : ContDiffAt ℂ ∞ T z := disc_chart_contDiffAt hf hz
  have huT : ContDiffAt ℝ ∞ (inChart y u) (T z) :=
    (hu y).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds
      (mem_extChartAt_target y))
  have hn : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hsrc : ∀ᶠ w in 𝓝 z, f w ∈ (extChartAt (ComplexModel n) y).source :=
    (hf.contMDiffAt hn).continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds y)
  have he : (fun w => u (f w)) =ᶠ[𝓝 z] (inChart y u) ∘ T := by
    filter_upwards [hsrc] with w hw
    exact (congrArg u ((extChartAt (ComplexModel n) y).left_inv hw)).symm
  exact (huT.comp z (hT.restrict_scalars ℝ)).congr_of_eventuallyEq he

theorem realPlanarLaplacian_eq_planarTrace {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    LeafCandidates.realPlanarLaplacian f z = P02Aux.planarTrace f z := by
  rw [L08_realPlanarLaplacian_eq_laplacian hf]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, P02Aux.planarTrace]

theorem smoothLevi_disc_laplacian_nonneg {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    0 ≤ LeafCandidates.realPlanarLaplacian (fun w => u (f w)) z := by
  have hactual : ContDiffAt ℝ 2 (fun w => u (f w)) z :=
    (smoothFn_disc_contDiffAt hu hf hz).of_le (by simp)
  obtain ⟨s, hs, heq, hlower, htrace⟩ := smoothLevi_disc_lowerSupports hu hL hf z hz
  let v : ℂ → ℝ := fun w => u (f w) + (-1) * s w
  have hneg : ContDiffAt ℝ 2 (fun w => (-1 : ℝ) * s w) z := contDiffAt_const.mul hs
  have hv : ContDiffAt ℝ 2 v z := hactual.add hneg
  have hmin : IsLocalMin v z := by
    change ∀ᶠ w in 𝓝 z, v z ≤ v w
    filter_upwards [hlower] with w hw
    dsimp only [v]
    linarith
  have hdiff := P02Aux.planarTrace_nonneg_of_localMin hv hmin
  change 0 ≤ P02Aux.planarTrace (fun w => u (f w) + (-1) * s w) z at hdiff
  rw [P02Aux.planarTrace_add _ _ z hactual hneg,
    P02Aux.planarTrace_const_mul s z hs (-1)] at hdiff
  rw [realPlanarLaplacian_eq_planarTrace hactual]
  linarith

theorem immersionPotential_disc_contDiffOn {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {f : ℂ → Pt X} (hf : IsHolomorphicDisc f) :
    ContDiffOn ℝ ∞ (fun z => immersionPotential X.metric.form F (f z))
      (Metric.ball (0 : ℂ) 1) :=
  fun _ hz => (smoothFn_disc_contDiffAt (immersionPotential_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm) hf hz).contDiffWithinAt

theorem immersionPotential_disc_laplacian_nonneg {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {f : ℂ → Pt X} (hf : IsHolomorphicDisc f) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    0 ≤ LeafCandidates.realPlanarLaplacian (fun w => immersionPotential X.metric.form F (f w)) z :=
  smoothLevi_disc_laplacian_nonneg (immersionPotential_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm)
    (immersionPotential_levi_posSemidef X hF hImm) hf hz

end Yau.NodeProofs.D02Aux
