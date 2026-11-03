import Yau.Proofs.F01ClampedFlowMatrix
import Yau.Proofs.F01ChartMetricOrder

/-! Native flow comparison bounds and actual background chart bounds
give the precise transformed-matrix range on the zero-extended slab. -/
noncomputable section
open Set
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem clamped_transformed_range_from_native_orders
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = α)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {ell upper c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbackground : ∀ z ∈ e.source,
      (pullbackMatrix α e z - (ell : ℂ) • 1).PosSemidef ∧
      ((upper : ℂ) • 1 - pullbackMatrix α e z).PosSemidef)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - (c : ℂ) • gMat α x).PosSemidef ∧
      ((C : ℂ) • gMat α x - gMat (h s) x).PosSemidef) :
    ∀ p ∈ e.source ×ˢ Icc (-1) T,
      (((clampedBackground (pullbackMatrix α e) p + complexHessianMap
          (hessian (forwardZeroSpaceTime (fun q : Point n => U (e q.1) q.2)) p) : Sym n) : Mat n) -
        (c * ell) • (1 : Mat n)).PosSemidef ∧
      ((C * upper) • (1 : Mat n) -
        ((clampedBackground (pullbackMatrix α e) p + complexHessianMap
          (hessian (forwardZeroSpaceTime (fun q : Point n => U (e q.1) q.2)) p) : Sym n) : Mat n)).PosSemidef := by
  intro p hp
  have hs : max p.2 0 ∈ Icc 0 T := ⟨le_max_right _ _, max_le hp.2.2 hT⟩
  have hnative := hflow (e p.1) (max p.2 0) hs
  have hlocal := relative_scalar_matrix_sandwich hc hC
    (hbackground p.1 hp.1).1 (hbackground p.1 hp.1).2
    (metric_lower_order_in_chart α (h (max p.2 0)) e p.1 hnative.1)
    (metric_upper_order_in_chart α (h (max p.2 0)) e p.1 hnative.2)
  have hreal := iota_scalar_matrix_sandwich hlocal.1 hlocal.2
  rw [clamped_flow_transformed_matrix α hα h U hU hh0 hpot e he hei hp.1 hp.2.2]
  exact hreal

end Yau.NodeProofs.F01Aux
