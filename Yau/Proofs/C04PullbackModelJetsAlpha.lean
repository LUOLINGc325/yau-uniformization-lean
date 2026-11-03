import Yau.Proofs.C04PullbackModelJetsGeometry

/-! All derivatives of the same rescaled inverse parameter on the larger
fixed ball. Linear precomposition is differentiated exactly. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pullbackModelParameterJetBudget (d : ℝ) (P : ℕ → ℝ) (m : ℕ) : ℝ :=
  d * P m * (5 / (4 * d)) ^ m

theorem pullbackModelParameterJetBudget_pos (d : ℝ) (hd : 0 < d)
    (P : ℕ → ℝ) (hP : ∀ m, 0 < P m) (m : ℕ) :
    0 < pullbackModelParameterJetBudget d P m := by
  dsimp [pullbackModelParameterJetBudget]
  have hp := hP m
  positivity

theorem pullback_model_parameter_jet_bound (d : ℝ) (hd : 0 < d)
    (P : ℕ → ℝ) (hP : ∀ m, 0 < P m)
    (ψ : E → E) (L : E →L[ℝ] E) (hL : ‖L‖ ≤ (5 / 4 : ℝ))
    (hψ : ContDiffOn ℝ ∞ ψ (Metric.ball (0 : E) (1 / 8 : ℝ)))
    (hjet : ∀ m w, w ∈ Metric.ball (0 : E) (1 / 8 : ℝ) →
      ‖iteratedFDeriv ℝ m ψ w‖ ≤ P m)
    (m : ℕ) {z : E} (hz : z ∈ Metric.ball (0 : E) (d / 16)) :
    ‖iteratedFDeriv ℝ m (pullbackModelParameter d ψ L) z‖ ≤
      pullbackModelParameterJetBudget d P m := by
  let T := pullbackModelLinear d L
  have hw : T z ∈ Metric.ball (0 : E) (1 / 8 : ℝ) :=
    pullback_model_linear_mem_ball d hd L hL hz
  have hpre : IsOpen (T ⁻¹' Metric.ball (0 : E) (1 / 8 : ℝ)) :=
    Metric.isOpen_ball.preimage T.continuous
  have heq := T.iteratedFDerivWithin_comp_right hψ Metric.isOpen_ball.uniqueDiffOn
    hpre.uniqueDiffOn hw (by simp : (m : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen m hpre hw,
    iteratedFDerivWithin_of_isOpen m Metric.isOpen_ball hw] at heq
  have hraw : ‖iteratedFDeriv ℝ m (ψ ∘ T) z‖ ≤ P m * (5 / (4 * d)) ^ m := by
    calc
      ‖iteratedFDeriv ℝ m (ψ ∘ T) z‖ =
          ‖(iteratedFDeriv ℝ m ψ (T z)).compContinuousLinearMap (fun _ => T)‖ :=
        congrArg norm heq
      _ ≤ ‖iteratedFDeriv ℝ m ψ (T z)‖ * ∏ _ : Fin m, ‖T‖ :=
        (iteratedFDeriv ℝ m ψ (T z)).norm_compContinuousLinearMap_le _
      _ = ‖iteratedFDeriv ℝ m ψ (T z)‖ * ‖T‖ ^ m := by simp
      _ ≤ P m * (5 / (4 * d)) ^ m :=
        mul_le_mul (hjet m (T z) hw)
          (pow_le_pow_left₀ (norm_nonneg T) (pullback_model_linear_norm d hd L hL) m)
          (pow_nonneg (norm_nonneg T) _) (hP m).le
  have hcomp : ContDiffAt ℝ ∞ (ψ ∘ T) z :=
    (hψ.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).comp z T.contDiff.contDiffAt
  have hscale := iteratedFDeriv_const_smul_apply' (a := d) (x := z)
    (hcomp.of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  change ‖iteratedFDeriv ℝ m (fun y => d • (ψ ∘ T) y) z‖ ≤ _
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
  exact (mul_le_mul_of_nonneg_left hraw hd.le).trans_eq (by
    dsimp [pullbackModelParameterJetBudget]
    ring)

end Yau.Proofs.C04Aux
