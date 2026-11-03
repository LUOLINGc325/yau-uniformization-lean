import Yau.Proofs.V03GagliardoCircle

/-! Bounded products satisfy a half-order Fourier estimate. The proof uses
only actual difference quotients and keeps ENNReal infinite endpoints. -/

open scoped Topology
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

def circleDifferenceDensity (u : AddCircle T → ℂ) (p : AddCircle T × AddCircle T) : ENNReal :=
  ENNReal.ofReal (‖u (p.2 + p.1) - u p.2‖ ^ 2 / ‖fourier 1 p.1 - 1‖ ^ 2)

theorem circleDifferenceDensity_measurable {u : AddCircle T → ℂ} (hu : Continuous u) :
    Measurable (circleDifferenceDensity u) := by
  unfold circleDifferenceDensity
  fun_prop

theorem circleGagliardo_eq_prod {u : AddCircle T → ℂ} (hu : Continuous u) :
    circleGagliardo u =
      ∫⁻ p, circleDifferenceDensity u p ∂(haarAddCircle.prod haarAddCircle) := by
  exact (lintegral_prod _ (circleDifferenceDensity_measurable hu).aemeasurable).symm

theorem circleDirichlet_le_of_square_bound {u v w : AddCircle T → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ x y, ‖w x - w y‖ ^ 2 ≤ A * ‖u x - u y‖ ^ 2 + B * ‖v x - v y‖ ^ 2) :
    circleDirichlet w ≤ ENNReal.ofReal A * circleDirichlet u +
      ENNReal.ofReal B * circleDirichlet v := by
  rw [← circleGagliardo_eq_dirichlet hu, ← circleGagliardo_eq_dirichlet hv,
    ← circleGagliardo_eq_dirichlet hw, circleGagliardo_eq_prod hu,
    circleGagliardo_eq_prod hv, circleGagliardo_eq_prod hw]
  calc
    (∫⁻ p, circleDifferenceDensity w p ∂(haarAddCircle.prod haarAddCircle)) ≤
      ∫⁻ p, ENNReal.ofReal A * circleDifferenceDensity u p +
        ENNReal.ofReal B * circleDifferenceDensity v p ∂(haarAddCircle.prod haarAddCircle) := by
      apply lintegral_mono
      intro p
      unfold circleDifferenceDensity
      dsimp only
      rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB,
        ← ENNReal.ofReal_add (mul_nonneg hA (by positivity)) (mul_nonneg hB (by positivity))]
      apply ENNReal.ofReal_le_ofReal
      have hh := div_le_div_of_nonneg_right (hbound (p.2 + p.1) p.2)
        (sq_nonneg ‖fourier 1 p.1 - 1‖)
      simpa only [add_div, mul_div_assoc] using hh
    _ = ENNReal.ofReal A * (∫⁻ p, circleDifferenceDensity u p ∂(haarAddCircle.prod haarAddCircle)) +
        ENNReal.ofReal B * (∫⁻ p, circleDifferenceDensity v p ∂(haarAddCircle.prod haarAddCircle)) := by
      rw [lintegral_add_left (f := fun p => ENNReal.ofReal A * circleDifferenceDensity u p)
        (measurable_const.mul (circleDifferenceDensity_measurable hu))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem circleDirichlet_mul_le {u v : AddCircle T → ℂ}
    (hu : Continuous u) (hv : Continuous v) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (huM : ∀ x, ‖u x‖ ≤ M) (hvN : ∀ x, ‖v x‖ ≤ N) :
    circleDirichlet (fun x => u x * v x) ≤
      ENNReal.ofReal (2 * N ^ 2) * circleDirichlet u +
      ENNReal.ofReal (2 * M ^ 2) * circleDirichlet v := by
  apply circleDirichlet_le_of_square_bound hu hv (hu.mul hv) (by positivity) (by positivity)
  intro x y
  change ‖u x * v x - u y * v y‖ ^ 2 ≤
    2 * N ^ 2 * ‖u x - u y‖ ^ 2 + 2 * M ^ 2 * ‖v x - v y‖ ^ 2
  have heq : u x * v x - u y * v y = (u x - u y) * v x + u y * (v x - v y) := by ring
  have hnorm := norm_add_le ((u x - u y) * v x) (u y * (v x - v y))
  rw [← heq, norm_mul, norm_mul] at hnorm
  have hb1 := mul_le_mul_of_nonneg_left (hvN x) (norm_nonneg (u x - u y))
  have hb2 := mul_le_mul_of_nonneg_right (huM y) (norm_nonneg (v x - v y))
  have hlin : ‖u x * v x - u y * v y‖ ≤ ‖u x - u y‖ * N + M * ‖v x - v y‖ := by linarith
  have hs := mul_self_le_mul_self (norm_nonneg _) hlin
  nlinarith [sq_nonneg (‖u x - u y‖ * N - M * ‖v x - v y‖)]

end Yau.Blueprint.V03Proof
