import Yau.Proofs.F01AffinePotentialSlice
import Yau.Proofs.F01ShiftedNativePotential

/-! The shifted native matrix identity is pointwise in the actual
clock interval. In particular it is valid at the final time and does
not require a positive-time neighborhood beyond it. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shifted_native_flow_matrix_at
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : ρ ≠ 0) (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) (p : Point n) (hz : ρ • p.1 ∈ ball 0 A.radius)
    (ht : τ + ρ ^ 2 * p.2 ∈ Icc 0 T) :
    chartPotentialMatrix (shiftedComplexBackground A a ρ τ) (shiftedNativePotential A U a ρ τ) p =
      pullbackMatrix (h (affineParabolicPoint ρ 0 τ p).2) (A.chart a)
        (affineParabolicPoint ρ 0 τ p).1 := by
  have hqz : (affineParabolicPoint ρ (0 : Space n) τ p).1 ∈ ball 0 A.radius := by
    simpa only [affineParabolicPoint, add_zero] using hz
  have hqt : (affineParabolicPoint ρ (0 : Space n) τ p).2 ∈ Icc 0 T := ht
  have hOld := (closed_slab_slice_jets (bounded_chart_spaceTime_smooth A hU a)
    isOpen_ball hqz hqt).1
  have hLevi := leviC_affineParabolicPotential_slice (ρ := ρ) (τ := τ) (p := p)
    (c := (0 : Space n)) (u := fun q : Point n => U (A.chart a q.1) q.2) hρ hOld
  change chartAffineBackground A a (affineParabolicPoint ρ 0 τ p) +
    leviC (fun z => affineParabolicPotential ρ 0 τ
      (fun q : Point n => U (A.chart a q.1) q.2) (z, p.2)) p.1 = _
  rw [hLevi]
  exact (flow_potential_matrix_in_chart g (h (affineParabolicPoint ρ 0 τ p).2) hg
    (fun x => U x (affineParabolicPoint ρ 0 τ p).2) (smoothSpaceTime_slice hU hqt)
    (affineParabolicPoint ρ 0 τ p).2 (hpot _ hqt) (A.chart a) (A.differentiable a)
    (A.inverse_differentiable a) (A.closedBall_source a (ball_subset_closedBall hqz))).symm

theorem shifted_backward_clock_maps {ρ τ T : ℝ} (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T) :
    MapsTo (fun t : ℝ => τ + ρ ^ 2 * t) (Icc (-1) 0) (Icc 0 T) := by
  intro t ht
  have hl := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg ρ)
  have hu := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg ρ)
  constructor <;> nlinarith

end Yau.NodeProofs.F01Aux
