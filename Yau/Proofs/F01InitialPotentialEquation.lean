import Yau.Proofs.F01IotaDeterminant
import Yau.Proofs.F01ClampedFlowMatrix
import Yau.Proofs.F01ZeroExtendedPotentialTime

/-! The original potential equation becomes exactly the initial-surface
equation for its actual zero extension, including both closed time faces. -/
noncomputable section
open Set
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem flowLogDetRatio_pullback_difference
    (α : HermitianField M) (h : ℝ → HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (t : ℝ) :
    flowLogDetRatio α h (e z) t =
      Real.log (pullbackMatrix (h t) e z).det.re - Real.log (pullbackMatrix α e z).det.re := by
  have hr := pullbackMatrix_determinant_ratio (h t) α e he hei (e z) hz
    (mem_extChartAt_source (e z))
  change (pullbackMatrix (h t) e z).det.re / (pullbackMatrix α e z).det.re =
    (gMat (h t) (e z)).det.re / (gMat α (e z)).det.re at hr
  unfold flowLogDetRatio
  rw [← hr]
  exact Real.log_div (Complex.pos_iff.mp (pullbackMatrix_posDef (h t) e he hei hz).det_pos).1.ne'
    (Complex.pos_iff.mp (pullbackMatrix_posDef α e he hei hz).det_pos).1.ne'

theorem zero_extended_potential_initial_equation
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ}
    (hT : 0 < T) (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = α)
    (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {p : Point n} (hp : p ∈ e.source ×ˢ Icc (-1) T) :
    timeD (e.source ×ˢ Icc (-1) T)
        (forwardZeroSpaceTime (fun q : Point n => U (e q.1) q.2)) p -
      logDetReal (clampedBackground (pullbackMatrix α e) p + complexHessianMap
        (hessian (forwardZeroSpaceTime (fun q : Point n => U (e q.1) q.2)) p)) =
      backgroundSource (pullbackMatrix α e) p := by
  rw [zero_extended_potential_timeD α h U hT hh0 hU0 hpde e hp,
    clamped_flow_transformed_matrix α hα h U hU hh0 hpot e he hei hp.1 hp.2.2,
    logDetReal_iota_posDef _ (pullbackMatrix_posDef (h (max p.2 0)) e he hei hp.1),
    flowLogDetRatio_pullback_difference α h e he hei hp.1]
  unfold backgroundSource
  ring

end Yau.NodeProofs.F01Aux
