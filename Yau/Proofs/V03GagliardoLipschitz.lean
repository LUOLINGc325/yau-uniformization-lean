import Yau.Proofs.V03GagliardoCircle

/-! Pointwise Lipschitz control yields the exact half-order Fourier
seminorm bound, also when either seminorm is infinite. -/

open scoped Topology NNReal
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem circleDirichlet_le_of_difference_bound {u v : AddCircle T → ℂ}
    (hu : Continuous u) (hv : Continuous v) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x y, ‖v x - v y‖ ≤ C * ‖u x - u y‖) :
    circleDirichlet v ≤ ENNReal.ofReal (C ^ 2) * circleDirichlet u := by
  rw [← circleGagliardo_eq_dirichlet hu, ← circleGagliardo_eq_dirichlet hv]
  unfold circleGagliardo
  calc
    (∫⁻ a : AddCircle T, ∫⁻ x : AddCircle T,
        ENNReal.ofReal (‖v (x + a) - v x‖ ^ 2 / ‖fourier 1 a - 1‖ ^ 2)
        ∂haarAddCircle ∂haarAddCircle) ≤
      ∫⁻ a : AddCircle T, ∫⁻ x : AddCircle T,
        ENNReal.ofReal (C ^ 2) *
          ENNReal.ofReal (‖u (x + a) - u x‖ ^ 2 / ‖fourier 1 a - 1‖ ^ 2)
        ∂haarAddCircle ∂haarAddCircle := by
      apply lintegral_mono
      intro a
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (sq_nonneg C)]
      apply ENNReal.ofReal_le_ofReal
      have hb := hbound (x + a) x
      have hsq : ‖v (x + a) - v x‖ ^ 2 ≤ C ^ 2 * ‖u (x + a) - u x‖ ^ 2 := by
        have hp := mul_self_le_mul_self (norm_nonneg _) hb
        nlinarith
      have hd := div_le_div_of_nonneg_right hsq (sq_nonneg ‖fourier 1 a - 1‖)
      simpa only [mul_div_assoc] using hd
    _ = ENNReal.ofReal (C ^ 2) *
      ∫⁻ a : AddCircle T, ∫⁻ x : AddCircle T,
        ENNReal.ofReal (‖u (x + a) - u x‖ ^ 2 / ‖fourier 1 a - 1‖ ^ 2)
        ∂haarAddCircle ∂haarAddCircle := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem circleDirichlet_lipschitz_comp {u : AddCircle T → ℂ} (hu : Continuous u)
    {f : ℂ → ℂ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    circleDirichlet (f ∘ u) ≤ ENNReal.ofReal ((C : ℝ) ^ 2) * circleDirichlet u := by
  apply circleDirichlet_le_of_difference_bound hu (hf.continuous.comp hu) C.coe_nonneg
  intro x y
  simpa only [Function.comp_def, dist_eq_norm] using hf.dist_le_mul (u x) (u y)

end Yau.Blueprint.V03Proof
