import Yau.Proofs.F04LeviComp
import Yau.Proofs.F04WeightedCross

open Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

set_option backward.isDefEq.respectTransparency false

open Yau.LeafProofs.L14Aux

def manifoldComplexGradient {n : ℕ} {M : ComplexManifold n} (f : M.Carrier → ℝ)
    (x : M.Carrier) : Fin n → ℂ := complexGradient (inChart x f) (chartPt x x)

theorem dual_norm_nonneg {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (c : Fin n → ℂ) :
    0 ≤ dualNormMat G (WithLp.toLp 2 c) :=
  (Complex.nonneg_iff.mp (hG.inv.transpose.posSemidef.dotProduct_mulVec_nonneg c)).1

theorem levi_mul {n : ℕ} {M : ComplexManifold n} {f g : M.Carrier → ℝ}
    (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    levi (fun y => f y * g y) x =
      (g x : ℂ) • levi f x + (f x : ℂ) • levi g x +
        covectorCross (manifoldComplexGradient f x) (manifoldComplexGradient g x) := by
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hO := (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hx
  have hcz := LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hh := leviC_mul (((hf x).contDiffAt hO).of_le (by norm_num))
    (((hg x).contDiffAt hO).of_le (by norm_num))
  convert hh using 1 <;>
    simp only [levi, manifoldComplexGradient, covectorCross, inChart, hcz, add_assoc]
  rfl

theorem levi_real_comp {n : ℕ} {M : ComplexManifold n} {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (F : ℝ → ℝ) (x : M.Carrier) (hF : ContDiffAt ℝ 2 F (f x)) :
    levi (fun y => F (f y)) x =
      ((deriv F (f x) : ℝ) : ℂ) • levi f x +
        ((deriv (deriv F) (f x) : ℝ) : ℂ) •
          Matrix.vecMulVec (star (manifoldComplexGradient f x)) (manifoldComplexGradient f x) := by
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hO := (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hx
  have hcz := LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hF' : ContDiffAt ℝ 2 F ((inChart x f) (chartPt x x)) := by
    simpa only [inChart, hcz] using hF
  have hh := leviC_real_comp (((hf x).contDiffAt hO).of_le (by norm_num)) hF'
  convert hh using 1 <;>
    simp only [levi, manifoldComplexGradient, inChart, hcz]
  rfl

theorem manifold_gradient_real_comp {n : ℕ} {M : ComplexManifold n} {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (F : ℝ → ℝ) (x : M.Carrier) {a : ℝ} (hF : HasDerivAt F a (f x)) :
    manifoldComplexGradient (fun y => F (f y)) x = scaleCovector a (manifoldComplexGradient f x) := by
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hO := (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hx
  have hcz := LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hF' : HasDerivAt F a ((inChart x f) (chartPt x x)) := by
    simpa only [inChart, hcz] using hF
  funext i
  exact (wirt_real_comp (((hf x).contDiffAt hO).differentiableAt (by simp)) hF' (stdVec i)).1

theorem gradNormSq_real_comp {n : ℕ} {M : ComplexManifold n} (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (F : ℝ → ℝ) (x : M.Carrier) {a : ℝ}
    (hF : HasDerivAt F a (f x)) :
    gradNormSq g (fun y => F (f y)) x = a ^ 2 * gradNormSq g f x := by
  change dualNormMat (gMat g x) (WithLp.toLp 2 (manifoldComplexGradient (fun y => F (f y)) x)) =
    a ^ 2 * dualNormMat (gMat g x) (WithLp.toLp 2 (manifoldComplexGradient f x))
  rw [manifold_gradient_real_comp hf F x hF]
  exact dual_norm_scale (gMat g x) (manifoldComplexGradient f x) a

end Yau.F04Proof
