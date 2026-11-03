import Yau.Proofs.F01NormalizedInitialPotential
import Yau.Proofs.F01ComplexBackgroundHolder

/-! The complex transformed matrix itself, before realification, is
identified with the same genuine native flow in the normalized initial
cylinder. This permits the canonical scalar symbol estimates on that field. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def normalizedComplexBackground (A : BoundedChartFamily g) (a : M.Carrier) (ρ : ℝ)
    (p : Point n) : Matrix (Fin n) (Fin n) ℂ :=
  pullbackMatrix g (A.chart a) (ρ • p.1) +
    max p.2 0 • (-(ρ ^ 2) • backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1))

theorem normalized_complex_flow_matrix
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = g)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    normalizedComplexBackground A a ρ p +
      leviC (fun z => forwardZeroSpaceTime
        (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2)) (z, p.2)) p.1 =
      pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) := by
  by_cases ht : p.2 ≤ 0
  · have heq : (fun z => forwardZeroSpaceTime
        (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2)) (z, p.2)) =
        fun _ => (0 : ℝ) := by
      funext z
      exact forwardZeroExtension_eq_of_nonpos _ ht
    rw [heq, leviC_const]
    simp only [normalizedComplexBackground, max_eq_right ht, zero_smul, add_zero, mul_zero, hh0]
  · have heq : (fun z => forwardZeroSpaceTime
        (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2)) (z, p.2)) =
        fun z => parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2) (z, p.2) := by
      funext z
      simp only [forwardZeroSpaceTime, forwardZeroExtension, ht, ite_false]
    rw [heq]
    have hpt : p ∈ ball 0 1 ×ˢ Icc 0 1 := ⟨hp.1, (lt_of_not_ge ht).le, hp.2.2⟩
    have hm : parabolicDilation ρ p ∈ ball 0 A.radius ×ˢ Icc 0 T :=
      parabolicDilation_maps_positive hρ hρr hρT hpt
    have hF := bounded_chart_spaceTime_smooth A hU a
    rw [parabolicRescalePotential_levi hρ.ne'
      (closed_slab_slice_jets hF isOpen_ball hm.1 hm.2).1,
      max_eq_left (lt_of_not_ge ht).le]
    have htime : ρ ^ 2 * p.2 ∈ Icc 0 T := hm.2
    have hz : ρ • p.1 ∈ (A.chart a).source := A.closedBall_source a (ball_subset_closedBall hm.1)
    rw [flow_potential_matrix_in_chart g (h (ρ ^ 2 * p.2)) hg
      (fun x => U x (ρ ^ 2 * p.2)) (smoothSpaceTime_slice hU htime)
      (ρ ^ 2 * p.2) (hpot _ htime) (A.chart a) (A.differentiable a) (A.inverse_differentiable a)
      (z := ρ • p.1) hz]
    simp only [normalizedComplexBackground, max_eq_left (lt_of_not_ge ht).le, Complex.coe_smul]
    module

end Yau.NodeProofs.F01Aux
