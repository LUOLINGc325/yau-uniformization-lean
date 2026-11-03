import Yau.LeafProofs.L21LeviCoefficientBounds
import Yau.LeafProofs.L21HermitianError

/-! The only weight-gradient error is the explicit corrected coefficient
error. Its small first jet absorbs uniformly in the singular boundary weight. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem levi_weight_error_entry_bound {K : ℝ} (hK : 0 ≤ K) {x : X n}
    (hx : x ∈ Metric.ball (0 : X n) 1)
    (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Fin n → Fin n → X n → ℂ) {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hE : ∀ i j b, ‖leviFirstCoefficient A d i j b x‖ ≤ C * ε) (i j : Fin n) :
    ‖∑ b : Yau.RIdx n, leviFirstCoefficient A d i j b x *
      fderiv ℝ (fun y : X n => (boundaryWeight K y : ℂ)) x (Yau.realVec b)‖ ≤
        (realDimension n : ℝ) * (C * ε * (2 * K * (rho x)⁻¹ ^ 2)) := by
  have hφ := ((contDiffOn_boundaryWeight K).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have hDp (b : Yau.RIdx n) :
      ‖fderiv ℝ (fun y : X n => (boundaryWeight K y : ℂ)) x (Yau.realVec b)‖ ≤
        2 * K * (rho x)⁻¹ ^ 2 := by
    rw [fderiv_ofReal_apply hφ, Complex.norm_real]
    have hh := ((fderiv ℝ (boundaryWeight K : X n → ℝ) x).le_opNorm (Yau.realVec b)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_boundaryWeight_le K hK hx) (norm_nonneg _))
    simpa only [mixedFrame_realVec_norm, mul_one] using hh
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : Yau.RIdx n, C * ε * (2 * K * (rho x)⁻¹ ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul]
      exact mul_le_mul (hE i j b) (hDp b) (norm_nonneg _) (mul_nonneg hC hε)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, realDimension]

theorem correctedLevi_boundaryWeight_lower_of_error {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (d : Fin n → Fin n → Fin n → X n → ℂ) {K : ℝ} (hK : 0 ≤ K)
    {x : X n} (hx : x ∈ O) (hxB : x ∈ Metric.ball (0 : X n) 1)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hE : ∀ i j b, ‖leviFirstCoefficient A d i j b x‖ ≤ C * ε)
    (hsmall : 2 * (n : ℝ) * (realDimension n : ℝ) * C * ε ≤ 1 / 2)
    (ξ : Fin n → ℂ) :
    (K / 2) * (rho x)⁻¹ ^ 2 * (∑ i, ‖ξ i‖ ^ 2) ≤
      (∑ i, ∑ j, star (ξ i) * correctedLevi A (boundaryWeight K) d i j x * ξ j).re := by
  let E (i j : Fin n) : ℂ := ∑ b : Yau.RIdx n, leviFirstCoefficient A d i j b x *
    fderiv ℝ (fun y : X n => (boundaryWeight K y : ℂ)) x (Yau.realVec b)
  let B : ℝ := (realDimension n : ℝ) * (C * ε * (2 * K * (rho x)⁻¹ ^ 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hErr := finite_hermitian_error_re_lower E ξ hB
    (levi_weight_error_entry_bound hK hxB A d hε hC hE)
  simp only [Fintype.card_fin] at hErr
  have hH := leviHessian_boundaryWeight_lower_bound hK hxB A ξ
  have hDecomp : (∑ i, ∑ j, star (ξ i) * correctedLevi A (boundaryWeight K) d i j x * ξ j).re =
      (∑ i, ∑ j, star (ξ i) * leviHessianPart A (boundaryWeight K) i j x * ξ j).re +
        (∑ i, ∑ j, star (ξ i) * E i j * ξ j).re := by
    have hWeight : ContDiffOn ℝ ∞ (boundaryWeight K : X n → ℝ) (O ∩ Metric.ball 0 1) :=
      (contDiffOn_boundaryWeight K).mono Set.inter_subset_right
    have hInt : IsOpen (O ∩ Metric.ball (0 : X n) 1) := hO.inter Metric.isOpen_ball
    have hAx : MatrixSmoothOn A (O ∩ Metric.ball 0 1) := fun i j => (hA i j).mono Set.inter_subset_left
    simp only [correctedLevi_hessian_decomposition hInt hAx hWeight d _ _ ⟨hx, hxB⟩,
      mul_add, add_mul, Finset.sum_add_distrib, Complex.add_re, E]
  have hAbsorb : (n : ℝ) * B * (∑ i, ‖ξ i‖ ^ 2) ≤
      (K / 2) * (rho x)⁻¹ ^ 2 * (∑ i, ‖ξ i‖ ^ 2) := by
    calc
      _ = (2 * (n : ℝ) * (realDimension n : ℝ) * C * ε) *
          (K * (rho x)⁻¹ ^ 2 * (∑ i, ‖ξ i‖ ^ 2)) := by dsimp [B]; ring
      _ ≤ (1 / 2 : ℝ) * (K * (rho x)⁻¹ ^ 2 * (∑ i, ‖ξ i‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := by ring
  linarith

end Yau.LeafProofs.L21Aux
