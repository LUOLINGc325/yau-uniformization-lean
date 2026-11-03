import Yau.Proofs.C03ChartMatrix
import Yau.Proofs.C03LogDual

/-! The original chart supplies one actual globally smooth log-dual
function, with the uniform logarithmic upper bound and normalized value. -/

noncomputable section
open Set
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def chartLogDual (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (ξ : ComplexVector n) : ComplexVector n → ℝ :=
  LogDual.logDual (fun z => gMat (chartExtendedField hn X Φ r hr hΦ) z) ξ

theorem chartLogDual_contDiff (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (ξ : ComplexVector n) (hξ : ξ ≠ 0) :
    ContDiff ℝ ∞ (chartLogDual hn X Φ r hr hΦ ξ) := by
  apply contDiffOn_univ.mp
  exact LogDual.logDual_contDiffOn _
    (fun i j => (chartExtendedField_gMat_contDiff hn X Φ r hr hΦ i j).contDiffOn)
    (fun z _ => chartExtendedField_gMat_posDef hn X Φ r hr hΦ z) ξ hξ

theorem chartLogDual_le (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (ξ : ComplexVector n) (hξ : ξ ≠ 0) (z : ComplexVector n) :
    chartLogDual hn X Φ r hr hΦ ξ z ≤
      max 0 (-Real.log (min c 1)) + 2 * Real.log (1 + ‖ξ‖) :=
  LogDual.logDual_le_of_lower _ z ξ hξ
    (chartExtendedField_gMat_posDef hn X Φ r hr hΦ z) (min c 1)
    (lt_min hc zero_lt_one) (chartExtendedField_lower hn X Φ r c hr hΦ hlo z)

theorem chartLogDual_zero (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (ξ : ComplexVector n)
    (hunit : dualNormMat (pullbackMat X.metric.form Φ 0) ξ = 1) :
    chartLogDual hn X Φ r hr hΦ ξ 0 = 0 := by
  apply LogDual.logDual_eq_zero_of_normalized
  change dualNormMat (gMat (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n)) ξ = 1
  rw [chartExtendedField_gMat_inner hn X Φ r hr hΦ (0 : ComplexVector n)
    (Metric.mem_closedBall_self (by positivity))]
  exact hunit

end Yau.Proofs.C03Aux
