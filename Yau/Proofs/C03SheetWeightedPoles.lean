import Yau.Proofs.C03SheetPoleLevi
import Yau.Proofs.C03PoleAbsorption

/-! One explicitly uniform scale makes the actual sheet poles globally
semipositive and strictly positive on the whole compact seed support. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem sheet_weighted_poles (O W : Set (ComplexVector n)) (hO : IsOpen O)
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (hθ : ContDiffOn ℂ ∞ θ O) (δp δs : ℝ) (hδp : 0 < δp) (hδps : δp ≤ δs)
    (m : ℕ) (w0 : ComplexVector n) (hsub : closedBall w0 δs ⊆ W)
    (C d κ : ℝ) (hC : 0 ≤ C) (hd : 0 < d) (hκ : 0 < κ)
    (hbound : ∀ j w v, -C * ‖v‖ ^ 2 ≤
      complexLeviQuadratic (TargetPole.translatedPole δp hδp m j w0) w v)
    (H : ComplexVector n → Herm n) (hHp : ∀ z, (H z).PosDef)
    (hD : ∀ z ∈ O, ∀ v,
      d * ‖fderiv ℂ θ z v‖ ^ 2 ≤ ellipsoidQuadratic (H z) v)
    (F : ComplexVector n → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFp : ∀ z, (leviC F z).PosSemidef)
    (hstrict : ∀ z ∈ σ '' closedBall w0 δs, HermLE ((κ : ℂ) • H z) (leviC F z)) :
    let k := (C / d + 1) / κ
    0 < k ∧ ContDiff ℝ ∞ (fun z => k * F z) ∧
      (∀ z, Antitone (fun j => sheetPole O θ δp hδp m w0 j z)) ∧
      ∀ j, ContDiff ℝ ∞ (sheetPole O θ δp hδp m w0 j) ∧
        HasCompactSupport (sheetPole O θ δp hδp m w0 j) ∧
        (∀ z, sheetPole O θ δp hδp m w0 j z ≤ 0) ∧
        (∀ z, (leviC (fun w => k * F w + sheetPole O θ δp hδp m w0 j w) z).PosSemidef) ∧
        ∀ z ∈ σ '' closedBall w0 δs,
          HermLE (H z) (leviC (fun w => k * F w + sheetPole O θ δp hδp m w0 j w) z) := by
  have hsubp : closedBall w0 δp ⊆ W := (closedBall_subset_closedBall hδps).trans hsub
  have hp (j : ℕ) := sheetPole_smooth_compact O W hO σ θ hσ hσW hστ
    (hθ.restrict_scalars ℝ) δp hδp m w0 hsubp j
  have hvanish (j : ℕ) (z : ComplexVector n) (hz : z ∉ σ '' closedBall w0 δs) :
      sheetPole O θ δp hδp m w0 j =ᶠ[𝓝 z] fun _ => 0 := by
    apply sheetPole_zero_germ O W σ θ hσ hσW hστ δp hδp m w0 hsubp j z
    exact fun H => hz (image_mono (closedBall_subset_closedBall hδps) H)
  obtain ⟨k, hkeq, hk, hw⟩ := exists_pole_absorbing_scale F hF hFp H hHp
    (σ '' closedBall w0 δs) κ (C / d) hκ (div_nonneg hC hd.le) hstrict
    (sheetPole O θ δp hδp m w0) (fun j => (hp j).1)
    (fun j z _ v => sheetPole_levi_lower O W hO σ θ hσ hσW hστ hθ
      δp hδp m w0 hsubp C d hC hd hbound H hHp hD j z v) hvanish
  subst k
  refine ⟨hk, contDiff_const.mul hF, sheetPole_antitone O θ δp hδp m w0, ?_⟩
  intro j
  exact ⟨(hp j).1, (hp j).2.1, sheetPole_nonpos O θ δp hδp m w0 j,
    (hw j).2.1, (hw j).2.2⟩

end Yau.Proofs.C03Aux
