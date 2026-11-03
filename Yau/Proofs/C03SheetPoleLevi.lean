import Yau.Proofs.C03SheetPole
import Yau.Proofs.C03LeviOrder

/-! Holomorphic pullback transports the uniform target pole Hessian
bound to the actual source metric; the zero extension has zero Levi off-sheet. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem sheetPole_levi_lower (O W : Set (ComplexVector n)) (hO : IsOpen O)
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (hθ : ContDiffOn ℂ ∞ θ O) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (w0 : ComplexVector n) (hsub : closedBall w0 δ ⊆ W)
    (C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d)
    (hbound : ∀ j w v, -C * ‖v‖ ^ 2 ≤
      complexLeviQuadratic (TargetPole.translatedPole δ hδ m j w0) w v)
    (H : ComplexVector n → Herm n) (hHp : ∀ z, (H z).PosDef)
    (hD : ∀ z ∈ O, ∀ v,
      d * ‖fderiv ℂ θ z v‖ ^ 2 ≤ ellipsoidQuadratic (H z) v)
    (j : ℕ) (z v : ComplexVector n) :
    -(C / d) * ellipsoidQuadratic (H z) v ≤
      complexLeviQuadratic (sheetPole O θ δ hδ m w0 j) z v := by
  by_cases hz : z ∈ O
  · have heq := sheetExtension_eq_comp_germ O hO θ
      (TargetPole.translatedPole δ hδ m j w0) z hz
    change sheetPole O θ δ hδ m w0 j =ᶠ[𝓝 z]
      TargetPole.translatedPole δ hδ m j w0 ∘ θ at heq
    rw [complexLeviQuadratic_congr_germ heq]
    rw [complexLeviQuadratic_comp
      (((hθ.contDiffAt (hO.mem_nhds hz)).of_le (by simp)))
      (((TargetPole.translatedPole_contDiff δ hδ m j w0).contDiffAt).of_le (by simp))]
    have hq := hD z hz v
    have hs : C * ‖fderiv ℂ θ z v‖ ^ 2 ≤
        (C / d) * ellipsoidQuadratic (H z) v := by
      have hdq := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hq)
      have hh := mul_le_mul_of_nonneg_left hdq hC
      convert hh using 1 <;> ring
    linarith [hbound j (θ z) (fderiv ℂ θ z v)]
  · have hz' : z ∉ σ '' closedBall w0 δ := by
      rintro ⟨w, hw, rfl⟩
      exact hz (hσW (hsub hw))
    rw [complexLeviQuadratic_congr_germ
      (sheetPole_zero_germ O W σ θ hσ hσW hστ δ hδ m w0 hsub j z hz') v,
      complexLeviQuadratic_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hC hd.le))
      (ellipsoidQuadratic_nonneg (hHp z).posSemidef v)

end Yau.Proofs.C03Aux
