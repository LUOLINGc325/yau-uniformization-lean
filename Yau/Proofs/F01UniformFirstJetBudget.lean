import Yau.Proofs.F01ClampedAffineHolder
import Yau.LeafProofs.L17UniformJets

/-! The actual first-jet bound on the native chart ball supplies one
supremum and Lipschitz budget, also after every smaller spatial dilation. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {ι E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_first_jet_budget {f : ι → E → F} {r : ℝ}
    (hf : UniformJetBounds 1 f (fun _ => ball 0 r))
    (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 r)) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ i x, x ∈ ball 0 r → ‖f i x‖ ≤ C) ∧
      (∀ i x, x ∈ ball 0 r → ∀ y, y ∈ ball 0 r →
        ‖f i x - f i y‖ ≤ C * ‖x - y‖) := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, ?_, ?_⟩
  · intro i x hx
    simpa only [norm_iteratedFDeriv_zero] using hb i x hx 0 (by omega)
  · intro i x hx y hy
    apply Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hs i).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp))
      (fun z hz => ?_) (convex_ball _ _) hy hx
    simpa only [norm_iteratedFDeriv_one] using hb i z hz 1 (by omega)

theorem uniform_first_jet_dilation_budget {f : ι → E → F} {r : ℝ}
    (hf : UniformJetBounds 1 f (fun _ => ball 0 r))
    (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 r)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ρ ≤ 1 →
      (∀ i x, x ∈ ball (0 : E) 1 → ‖f i (ρ • x)‖ ≤ C) ∧
      (∀ i x, x ∈ ball (0 : E) 1 → ∀ y, y ∈ ball (0 : E) 1 →
        ‖f i (ρ • x) - f i (ρ • y)‖ ≤ C * ‖x - y‖) := by
  obtain ⟨C, hC, hb, hl⟩ := uniform_first_jet_budget hf hs
  refine ⟨C, hC, ?_⟩
  intro ρ hρ hρr hρ1
  have hmap {x : E} (hx : x ∈ ball (0 : E) 1) : ρ • x ∈ ball (0 : E) r := by
    have hx1 : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] using
      (mul_lt_mul_of_pos_left hx1 hρ).trans_le (by simpa using hρr)
  refine ⟨fun i x hx => hb i _ (hmap hx), ?_⟩
  intro i x hx y hy
  calc
    _ ≤ C * ‖ρ • x - ρ • y‖ := hl i _ (hmap hx) _ (hmap hy)
    _ = C * (ρ * ‖x - y‖) := by rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    _ ≤ C * ‖x - y‖ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) hρ1) (zero_le_one.trans hC)

end Yau.NodeProofs.F01Aux
