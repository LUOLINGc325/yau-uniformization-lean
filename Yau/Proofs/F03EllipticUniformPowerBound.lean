import Yau.Proofs.F03EllipticPowers
import Yau.Proofs.F03CompactPowerIntegral

/-! Actual bounded elliptic powers give a uniform tensor bound, with the constant before every function. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafCandidates LeafProofs
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem elliptic_tensor_bound_of_uniform_powers
    (n : ℕ) (hn : 0 < n) (m N : ℕ) (hOrder : m+n < 2*N)
    (r R ell A : ℝ) (hr : 0 < r) (hrR : r < R) (hell : 0 < ell) (hA : 0 < A) :
    ∃ C : ℝ,0 < C ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
      (∀ i j,ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 R)) →
      (∀ i,ContDiffOn ℝ ∞ (fun z => b z i) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball 0 R,∀ v : RIdx n → ℝ,
        ell * ∑ i,(v i)^2 ≤ ∑ i,∑ j,a z i j*v i*v j) →
      (∀ k ≤ 2*N+1,∀ z ∈ Metric.ball 0 R,∀ i j,
        ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A) →
      ∀ (D : Set (ComplexVector n)),IsOpen D → Metric.closedBall 0 R ⊆ D →
      ∀ u : ComplexVector n → ℂ,
      (∀ p ≤ N,ContDiffOn ℝ ∞ ((ellipticOp a b)^[p] u) D) →
      ∀ B : ℝ,0 ≤ B →
      (∀ p ≤ N,∀ z ∈ Metric.ball 0 R,‖((ellipticOp a b)^[p] u) z‖ ≤ B) →
      ∀ z ∈ Metric.ball 0 r,‖iteratedFDeriv ℝ m u z‖ ≤ C*B := by
  obtain ⟨CT,hCT,hTensor⟩ := elliptic_power_tensor_bound n hn m N hOrder r R ell A hr hrR hell hA
  let V := (lebesgueC n).real (Metric.ball (0 : ComplexVector n) R)
  let Q := (N+1 : ℝ)*V
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hQ : 0 ≤ Q := mul_nonneg (by positivity) hV
  have hFin : lebesgueC n (Metric.ball (0 : ComplexVector n) R) ≠ ⊤ := by
    rw [lebesgueC_eq_volume]
    exact (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : ComplexVector n) R).measure_lt_top).ne
  refine ⟨CT*(Real.sqrt Q+1),mul_pos hCT (by positivity),?_⟩
  intro a b ha hb hEll hBound D hD hBall u hu B hB hUniform z hz
  have hSub : Metric.ball (0 : ComplexVector n) R ⊆ D := Metric.ball_subset_closedBall.trans hBall
  have hI : ∀ p ≤ N,∀ j : ℕ,IntegrableOn
      (fun w => ‖iteratedFDeriv ℝ j ((ellipticOp a b)^[p] u) w‖^2)
      (Metric.ball 0 R) (lebesgueC n) := fun p hp j =>
    smooth_chart_jet_square_integrable_ball D hD _ (hu p hp) R hBall j
  have hValueI : ∀ p ≤ N,IntegrableOn
      (fun w => ‖((ellipticOp a b)^[p] u) w‖^2) (Metric.ball 0 R) (lebesgueC n) := by
    intro p hp
    simpa only [norm_iteratedFDeriv_zero] using hI p hp 0
  have hIntegral := finite_power_integral_sq_le (lebesgueC n) (Metric.ball 0 R)
    measurableSet_ball hFin N (fun p => (ellipticOp a b)^[p] u) hValueI B hB hUniform
  have hSquareRoot : Real.sqrt (∑ p ∈ Finset.range (N+1),
      ∫ w in Metric.ball 0 R,‖((ellipticOp a b)^[p] u) w‖^2 ∂lebesgueC n) ≤ Real.sqrt Q*B := by
    change (∑ p ∈ Finset.range (N+1),
      ∫ w in Metric.ball 0 R,‖((ellipticOp a b)^[p] u) w‖^2 ∂lebesgueC n) ≤ Q*B^2 at hIntegral
    have h := Real.sqrt_le_sqrt hIntegral
    simpa only [Real.sqrt_mul hQ,Real.sqrt_sq_eq_abs,abs_of_nonneg hB] using h
  have hT := hTensor a b ha hb hEll hBound u (fun p hp => (hu p hp).mono hSub)
    (fun p hp j _hj => hI p hp j) z hz
  calc
    _ ≤ CT*(Real.sqrt Q*B) := hT.trans (mul_le_mul_of_nonneg_left hSquareRoot hCT.le)
    _ ≤ CT*(Real.sqrt Q+1)*B := by nlinarith [mul_nonneg hCT.le hB]

end Yau.Proofs.F03Aux
