import Yau.Proofs.C02ChernCoefficientCone
import Yau.Proofs.G01RealRmChern

/-! The original real curvature calculator is the real contraction of
our actual Chern coefficient array; its last-pair skewness is computed
from the actual metric-compatible Levi--Civita connection. -/

noncomputable section
open scoped Matrix Manifold
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem actualChernArray_real_evaluation (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (p : M.Carrier) (u v w z : ComplexVector n) :
    realCurvatureEvaluation (actualChernArray h p) (WithLp.ofLp u) (WithLp.ofLp v)
      (WithLp.ofLp w) (WithLp.ofLp z) = realRmInChart h p (chartPt p p) u v w z := by
  rw [realRmInChart_eq_chern h hs hk p (chartPt p p) (mem_extChartAt_target p)]
  unfold realCurvatureEvaluation curvatureEvaluation actualChernArray
  congr 1
  apply congrArg Complex.re
  simp only [Finset.sum_mul, mul_sub, ← Finset.sum_sub_distrib]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a0 _
  apply Finset.sum_congr rfl
  intro a1 _
  apply Finset.sum_congr rfl
  intro a2 _
  apply Finset.sum_congr rfl
  intro a3 _
  rw [chernInChart_center]
  ring

theorem realRmInChart_swap_last (g : SmoothMetric M) (p : M.Carrier)
    (y : ComplexVector n) (hy : y ∈ chartTarget p) (u v w z : ComplexVector n) :
    realRmInChart g.form p y u v w z = -realRmInChart g.form p y u v z w := by
  unfold realRmInChart
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [curvature4_swap_last g p y hy a b c d]
  ring

end Yau.Blueprint.C02Proof
