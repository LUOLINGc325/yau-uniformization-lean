import Yau.Proofs.P07ProfilesScalar
import Yau.Proofs.P07Affine
import Yau.Proofs.P07MatrixOrder
import Yau.Proofs.P07DistanceLeviRankOne

/-! Fixed scalar stepping gives true local plateaux and retains all
quantitative derivative bounds of the same actual smooth function. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem cutoffTransition_derivative_bounds :
    ∃ B1 B2 : ℝ, 0 < B1 ∧ 0 < B2 ∧
      ∀ s, |deriv cutoffTransition s| ≤ B1 ∧ |deriv (deriv cutoffTransition) s| ≤ B2 :=
  exists_plateau_derivative_bounds cutoffTransition cutoffTransition_contDiff (1 / 4) (3 / 4) 0 1
    (fun _ hs => cutoffTransition_zero hs) (fun _ hs => cutoffTransition_one hs)

theorem step_locally_zero {w : M.Carrier → ℝ} (hw : Continuous w) {x : M.Carrier}
    (hx : w x ≤ 1 / 16) :
    (fun y => cutoffTransition (w y)) =ᶠ[𝓝 x] fun _ => 0 := by
  have hlt : w x < 1 / 4 := by linarith
  filter_upwards [hw.continuousAt.eventually (Iio_mem_nhds hlt)] with y hy
  exact cutoffTransition_zero hy.le

theorem step_locally_one {w : M.Carrier → ℝ} (hw : Continuous w) {x : M.Carrier}
    (hx : 15 / 16 ≤ w x) :
    (fun y => cutoffTransition (w y)) =ᶠ[𝓝 x] fun _ => 1 := by
  have hlt : 3 / 4 < w x := by linarith
  filter_upwards [hw.continuousAt.eventually (Ioi_mem_nhds hlt)] with y hy
  exact cutoffTransition_one hy.le

theorem scalar_comp_directional_bound (g : SmoothMetric M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    {B1 B2 A G : ℝ} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hθ1 : ∀ s, |deriv θ s| ≤ B1) (hθ2 : ∀ s, |deriv (deriv θ) s| ≤ B2)
    (hgrad : ∀ x, gradNormSq g.form f x ≤ G)
    (hlevi : ∀ x v, |leviDirection (levi f x) v| ≤ A * leviDirection (gMat g.form x) v) :
    ∀ x v, |leviDirection (levi (fun y => θ (f y)) x) v| ≤
      (B1 * A + 2 * B2 * G) * leviDirection (gMat g.form x) v := by
  intro x v
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hval : inChart x f (chartPt x x) = f x :=
    congrArg f ((extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x))
  have hchain := P07DistanceLevi.leviDirection_scalar_comp
    ((contDiffAt_inChart hf x hz).of_le (by simp))
    (show ContDiffAt ℝ 2 θ (inChart x f (chartPt x x)) from
      hval ▸ hθ.contDiffAt.of_le (by simp)) v
  change leviDirection (levi (fun y => θ (f y)) x) v =
    deriv θ (inChart x f (chartPt x x)) * leviDirection (levi f x) v +
    deriv (deriv θ) (inChart x f (chartPt x x)) *
      P07DistanceLevi.directionalRankOne (inChart x f) (chartPt x x) v at hchain
  rw [hval] at hchain
  have hH : 0 ≤ leviDirection (gMat g.form x) v :=
    (Complex.nonneg_iff.mp ((Yau.LeafProofs.L12Aux.hMat_posDef g.form x (chartPt x x) hz).posSemidef.dotProduct_mulVec_nonneg
      (WithLp.ofLp v))).1
  have hR := P07DistanceLevi.directionalRankOne_nonneg (inChart x f) (chartPt x x) v
  have hRb := P07DistanceLevi.directionalRankOne_inChart_le g.form hf x v
  have hRb' : P07DistanceLevi.directionalRankOne (inChart x f) (chartPt x x) v ≤
      2 * G * leviDirection (gMat g.form x) v := by
    nlinarith [mul_le_mul_of_nonneg_right (hgrad x) hH]
  rw [hchain]
  calc
    _ ≤ |deriv θ (f x) * leviDirection (levi f x) v| +
        |deriv (deriv θ) (f x) * P07DistanceLevi.directionalRankOne (inChart x f) (chartPt x x) v| :=
      abs_add_le _ _
    _ = |deriv θ (f x)| * |leviDirection (levi f x) v| +
        |deriv (deriv θ) (f x)| * P07DistanceLevi.directionalRankOne (inChart x f) (chartPt x x) v := by
      rw [abs_mul, abs_mul, abs_of_nonneg hR]
    _ ≤ B1 * (A * leviDirection (gMat g.form x) v) +
        B2 * (2 * G * leviDirection (gMat g.form x) v) :=
      add_le_add (mul_le_mul (hθ1 _) (hlevi x v) (abs_nonneg _) hB1)
        (mul_le_mul (hθ2 _) hRb' hR hB2)
    _ = _ := by ring

end Yau.NodeProofs.P07Aux
