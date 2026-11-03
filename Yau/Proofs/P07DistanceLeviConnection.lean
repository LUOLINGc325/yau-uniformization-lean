import Yau.Proofs.G01ConnectionJ
import Yau.LeafProofs.L23DistanceEnergyHessian
import Yau.Proofs.P07DistanceLeviCalculus

/-! The Kähler connection cancels in the paired complex-line Hessian. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L22Aux L19Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem realCoord_I_smul (v : ComplexVector n) (a : RIdx n) :
    realCoord (Complex.I • v) a =
      jSign (jIndex n a) * realCoord v (jIndex n a) := by
  rcases a with ⟨i,a⟩
  fin_cases a <;> simp [realCoord, jIndex, jSign, Complex.mul_re, Complex.mul_im]

/-- The genuine connection is complex-linear in its transported vector. -/
theorem chartChristoffelBilin_I_right
    (h : HermitianField M) (hh : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (u v : ComplexVector n) :
    chartChristoffelBilin h x z u (Complex.I • v) =
      Complex.I • chartChristoffelBilin h x z u v := by
  apply realCoord_injective n
  funext c
  rw [realCoord_I_smul, chartChristoffelBilin_apply,
    chartChristoffelBilin_apply, realCoord_sum_realVec, realCoord_sum_realVec,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  calc
    (∑ b, christoffel h x z c a b * realCoord u a * realCoord (Complex.I • v) b) =
        ∑ b, christoffel h x z c a (jIndex n b) * realCoord u a *
          realCoord (Complex.I • v) (jIndex n b) :=
      ((jIndex n).sum_comp (fun b => christoffel h x z c a b * realCoord u a *
        realCoord (Complex.I • v) b)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [realCoord_I_smul, jIndex_involutive]
      calc
        _ = (jSign b * christoffel h x z c a (jIndex n b)) * realCoord u a * realCoord v b := by ring
        _ = _ := by
          rw [G01Aux.christoffel_jIndex h hh hk x z hz a b c]
          ring

theorem chartChristoffelBilin_I_left
    (h : HermitianField M) (hh : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (u v : ComplexVector n) :
    chartChristoffelBilin h x z (Complex.I • u) v =
      Complex.I • chartChristoffelBilin h x z u v := by
  rw [chartChristoffelBilin_symm h x z (Complex.I • u) v,
    chartChristoffelBilin_I_right h hh hk x hz,
    chartChristoffelBilin_symm h x z v u]

theorem chartChristoffelBilin_I_I
    (h : HermitianField M) (hh : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (u v : ComplexVector n) :
    chartChristoffelBilin h x z (Complex.I • u) (Complex.I • v) =
      -chartChristoffelBilin h x z u v := by
  rw [chartChristoffelBilin_I_right h hh hk x hz,
    chartChristoffelBilin_I_left h hh hk x hz, smul_smul, Complex.I_mul_I, neg_one_smul]

/-- At every point of every holomorphic chart, the Levi quadratic is the
paired covariant Hessian divided by four, with the original metric. -/
theorem leviDirection_eq_paired_covariantHessian
    (h : HermitianField M) (hh : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    {f : ComplexVector n → ℝ} (hf : ContDiffAt ℝ 2 f z) (v : ComplexVector n) :
    leviDirection (leviC f z) v =
      (chartCovHessianBilin h x f z v v +
        chartCovHessianBilin h x f z (Complex.I • v) (Complex.I • v)) / 4 := by
  rw [leviDirection, leviC_quadratic_re hf]
  unfold complexLeviQuadratic
  rw [L19Aux.chartCovHessianBilin_apply, L19Aux.chartCovHessianBilin_apply,
    chartChristoffelBilin_I_I h hh hk x hz, map_neg]
  ring

end Yau.NodeProofs.P07DistanceLevi
