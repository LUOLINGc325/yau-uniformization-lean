import Yau.Proofs.C01SmoothPaths
import Yau.Proofs.C01MetricMonotonicity

/-! The actual speed of a path is the central-chart metric quadratic
form used by the original scalar differential Harnack inequality. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def pathChartVelocity {x y : M.Carrier} (γ : PiecewiseC1Curve x y) (s : ℝ) : ComplexVector n :=
  fderiv ℝ (fun u : ℝ => extChartAt (ComplexModel n) (γ s) (γ u)) s 1

theorem center_metric_quadratic_eq_normSq (g : HermitianField M) (x : M.Carrier)
    (v : ComplexVector n) :
    (star (WithLp.ofLp v) ⬝ᵥ (gMat g x *ᵥ WithLp.ofLp v)).re =
      hermitianNormSq (g x) (chartVec x x v) := by
  have hcenter : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hq := Yau.Blueprint.Alignment.Y03Proof.hMat_quadratic g x (chartPt x x) (WithLp.ofLp v)
  rw [hcenter, chartVec_basis_sum] at hq
  simpa only [gMat, hermitianNormSq] using congrArg Complex.re hq

theorem curveSpeed_sq_eq_center_quadratic (g : HermitianField M) {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) (s : ℝ) :
    curveSpeed g γ s ^ 2 =
      2 * (star (WithLp.ofLp (pathChartVelocity γ s)) ⬝ᵥ
        (gMat g (γ s) *ᵥ WithLp.ofLp (pathChartVelocity γ s))).re := by
  rw [center_metric_quadratic_eq_normSq]
  unfold curveSpeed
  rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (hermitianNormSq_nonneg (g (γ s)) (realTangentDerivative γ s)))]
  rfl

variable {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_path_metric_quadratic_le
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    {x y : Pt X} (γ : PiecewiseC1Curve x y) (s a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    (star (WithLp.ofLp (pathChartVelocity γ s)) ⬝ᵥ
      (gMat (h t) (γ s) *ᵥ WithLp.ofLp (pathChartVelocity γ s))).re ≤
        curveSpeed (h a) γ s ^ 2 / 2 := by
  have hm := localizedFlow_metric_monotonicity hflow hjoint (γ s) a t ha hat
  change (gMat (h a) (γ s) - gMat (h t) (γ s)).PosSemidef at hm
  have hq := (Complex.nonneg_iff.mp
    (hm.dotProduct_mulVec_nonneg (WithLp.ofLp (pathChartVelocity γ s)))).1
  simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at hq
  have hs := curveSpeed_sq_eq_center_quadratic (h a) γ s
  linarith

end Yau.NodeProofs.C01Aux
