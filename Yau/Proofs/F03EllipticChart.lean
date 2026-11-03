import Yau.Proofs.F03EllipticComplexification
import Yau.Proofs.F03CompactHeatError
import Yau.LeafProofs.L19HeatRegularityWeakEquation

/-! The actual chart elliptic operator and all its powers are the computed physical Laplacian powers. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem ellipticOp_congr_eventuallyEq
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) {f k : ComplexVector n → ℂ} {z : ComplexVector n}
    (heq : f =ᶠ[𝓝 z] k) : ellipticOp a b f z=ellipticOp a b k z := by
  have hFirst (v : ComplexVector n) : fderiv ℝ f z v=fderiv ℝ k z v :=
    congrArg (fun A : ComplexVector n →L[ℝ] ℂ => A v) heq.fderiv_eq
  have hSecond (v w : ComplexVector n) :
      fderiv ℝ (fun y => fderiv ℝ f y w) z v=fderiv ℝ (fun y => fderiv ℝ k y w) z v := by
    have hD : (fun y => fderiv ℝ f y w) =ᶠ[𝓝 z] (fun y => fderiv ℝ k y w) :=
      (show fderiv ℝ f =ᶠ[𝓝 z] fderiv ℝ k from heq.fderiv).mono
        (fun _ hy => congrArg (fun A : ComplexVector n →L[ℝ] ℂ => A w) hy)
    exact congrArg (fun A : ComplexVector n →L[ℝ] ℂ => A v) hD.fderiv_eq
  simp only [ellipticOp,hFirst,hSecond]

theorem realEllipticOp_chart_laplacian (g : SmoothMetric M) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    realEllipticOp (fun w => scalarHeatChartCoeff g a (w,0)) (fun _ _ => 0)
      (inChart a u) z=laplacian g.form u (chartInv a z) := by
  have hU : ContDiffAt ℝ 2 (inChart a u) z :=
    ((hu a).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).of_le (by simp)
  have hL := principal_realLaplacian_eq_twice_traceWith g.form a hz hU
  have hTrace := traceWith_inChart_eq_laplacian g.form hu a hz
  unfold realEllipticOp
  simp only [zero_mul,Finset.sum_const_zero,add_zero]
  calc
    _ = (1/2 : ℝ)*(∑ i,∑ j,(realMetricFn g.form a z)⁻¹ i j*
        fderiv ℝ (fderiv ℝ (inChart a u)) z (realVec i) (realVec j)) := by
      simp only [scalarHeatChartCoeff,Finset.mul_sum,mul_assoc]
    _ = laplacian g.form u (chartInv a z) := by rw [hL,hTrace];ring

theorem ellipticOp_chart_laplacian (g : SmoothMetric M) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    ellipticOp (fun w => scalarHeatChartCoeff g a (w,0)) (fun _ _ => 0)
      (fun w => (inChart (α := ℝ) a u w : ℂ)) z=(laplacian g.form u (chartInv a z) : ℂ) := by
  have hU := (hu a).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)
  exact (ellipticOp_ofReal (fun w => scalarHeatChartCoeff g a (w,0)) (fun _ _ => 0)
    (u := inChart a u) hU).trans
      (congrArg Complex.ofReal (realEllipticOp_chart_laplacian g hu a hz))

theorem ellipticOp_chart_laplacian_power (g : SmoothMetric M) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (a : M.Carrier) (m : ℕ) :
    EqOn ((ellipticOp (fun w => scalarHeatChartCoeff g a (w,0)) (fun _ _ => 0))^[m]
      (fun w => (inChart (α := ℝ) a u w : ℂ)))
      (fun w => (inChart (α := ℝ) a ((laplacian g.form)^[m] u) w : ℂ)) (chartTarget a) := by
  induction m with
  | zero => exact fun _ _ => rfl
  | succ m ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hEq : ((ellipticOp (fun w => scalarHeatChartCoeff g a (w,0)) (fun _ _ => 0))^[m]
        (fun w => (inChart (α := ℝ) a u w : ℂ))) =ᶠ[𝓝 z]
        (fun w => (inChart (α := ℝ) a ((laplacian g.form)^[m] u) w : ℂ)) := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz] with w hw
      exact ih hw
    rw [ellipticOp_congr_eventuallyEq _ _ hEq,
      ellipticOp_chart_laplacian g (smoothFn_laplacian_power g hu m) a hz,
      Function.iterate_succ_apply']
    rfl

end Yau.Proofs.F03Aux
