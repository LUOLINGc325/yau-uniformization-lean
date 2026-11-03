import Yau.Proofs.F01ShiftedPointLogData
import Yau.Proofs.F01ScalarChartSmooth

/-! The normalized matrix of one actual smooth potential slice is
the same native positive Hermitian field in the original chart. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem normalized_native_slice_matrix_at
    (hg : MetricSmooth g) (A : BoundedChartFamily g) (K : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) {σ T : ℝ} (hσ : σ ≠ 0)
    (a : M.Carrier) (p : Point n) (hz : σ • p.1 ∈ ball 0 A.radius)
    (hpot : ∀ y, gMat K y = gMat g y - ((T + σ ^ 2 * p.2 : ℝ) : ℂ) • ricci g y + levi u y) :
    chartPotentialMatrix (shiftedComplexBackground A a σ T)
      (fun q : Point n => (σ ^ 2)⁻¹ * u (A.chart a (σ • q.1))) p =
      pullbackMatrix K (A.chart a) (σ • p.1) := by
  have hSource : σ • p.1 ∈ (A.chart a).source :=
    A.closedBall_source a (ball_subset_closedBall hz)
  have hChart := smoothFn_comp_holomorphic_chart u hu (A.chart a) (A.differentiable a)
  have hAt : ContDiffAt ℝ 2 (fun z => u (A.chart a z)) (σ • p.1) :=
    (hChart.contDiffAt ((A.chart a).open_source.mem_nhds hSource)).of_le (by simp)
  have hLevi := leviC_affineParabolicPotential_slice (ρ := σ) (τ := T) (c := 0)
    (u := fun q : Point n => u (A.chart a q.1)) (p := p) hσ
    (by simpa only [affineParabolicPoint, add_zero] using hAt)
  have hLevi' : leviC (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z))) p.1 =
      leviC (fun z => u (A.chart a z)) (σ • p.1) := by
    simpa only [affineParabolicPotential, affineParabolicPullback, affineParabolicPoint,
      add_zero] using hLevi
  change chartAffineBackground A a (affineParabolicPoint σ 0 T p) +
    leviC (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z))) p.1 = _
  rw [hLevi']
  have hh := flow_potential_matrix_in_chart g K hg u hu (T + σ ^ 2 * p.2)
    hpot (A.chart a) (A.differentiable a) (A.inverse_differentiable a) hSource
  simpa only [chartAffineBackground, affineParabolicPoint, add_zero] using hh.symm

end Yau.NodeProofs.F01Aux
