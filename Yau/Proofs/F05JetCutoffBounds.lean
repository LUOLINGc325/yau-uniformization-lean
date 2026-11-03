import Yau.Proofs.F05JetCutoffContinuity
import Yau.Proofs.F05JetNorms
import Yau.LeafProofs.L16ChartCutoffBudget

/-! A fixed smooth compact cutoff has a uniform raw jet budget before the
physical set, exponent, or jet is chosen. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

local instance f05_cutoffBoundDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_cutoffBoundDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_cutoffBoundHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_cutoffBoundHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05JetComponent_hessian_bound {α : ℝ} {Q : Set (Point n)}
    (u : F05JetComponent α Q) (p : Point n) : ‖F05BCFFun u.2.2.1.val.1 p‖ ≤ ‖u‖ := by
  have h0 : ‖u.2.2.1.val.1‖ ≤ ‖u.2.2.1‖ := le_max_left _ _
  have h1 : ‖u.2.2.1‖ ≤ ‖u‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact (F05BCFFun_norm_le u.2.2.1.val.1 p).trans (h0.trans h1)

theorem F05JetComponent_time_bound {α : ℝ} {Q : Set (Point n)}
    (u : F05JetComponent α Q) (p : Point n) : ‖F05BCFFun u.2.2.2.val.1 p‖ ≤ ‖u‖ := by
  have h0 : ‖u.2.2.2.val.1‖ ≤ ‖u.2.2.2‖ := le_max_left _ _
  have h1 : ‖u.2.2.2‖ ≤ ‖u‖ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact (F05BCFFun_norm_le u.2.2.2.val.1 p).trans (h0.trans h1)

theorem F05_cutoff_jet_raw_bound_of_bound {E : ℝ} (hE : 0 ≤ E)
    (φ : Space n → ℝ)
    (hφ : ∀ x, |φ x| ≤ E ∧ ‖fderiv ℝ φ x‖ ≤ E ∧ ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ E)
    {α : ℝ} {Q : Set (Point n)} (u : F05JetComponent α Q) (p : Point n) :
    |F05CutoffJetValue φ u p| ≤ 4*E*‖u‖ ∧
      ‖F05CutoffJetGradient φ u p‖ ≤ 4*E*‖u‖ ∧
      ‖F05CutoffJetHessian φ u p‖ ≤ 4*E*‖u‖ ∧
      |F05CutoffJetTime φ u p| ≤ 4*E*‖u‖ := by
  have hV : |F05BCFFun u.1 p| ≤ ‖u‖ := F05JetComponent_value_bound u p
  have hG := F05JetComponent_gradient_bound u p
  have hH := F05JetComponent_hessian_bound u p
  have hK : |F05BCFFun u.2.2.2.val.1 p| ≤ ‖u‖ := F05JetComponent_time_bound u p
  have h0 := (hφ p.1).1
  have h1 := (hφ p.1).2.1
  have h2 := (hφ p.1).2.2
  have hEK : 0 ≤ E*‖u‖ := mul_nonneg hE (norm_nonneg u)
  have hValue : |F05CutoffJetValue φ u p| ≤ E*‖u‖ := by
    unfold F05CutoffJetValue
    rw [abs_mul]
    exact mul_le_mul h0 hV (abs_nonneg _) hE
  have hTime : |F05CutoffJetTime φ u p| ≤ E*‖u‖ := by
    unfold F05CutoffJetTime
    rw [abs_mul]
    exact mul_le_mul h0 hK (abs_nonneg _) hE
  have hGradient : ‖F05CutoffJetGradient φ u p‖ ≤ 2*E*‖u‖ := by
    unfold F05CutoffJetGradient
    calc
      _ ≤ ‖φ p.1 • F05BCFFun u.2.1 p‖ + ‖F05BCFFun u.1 p • fderiv ℝ φ p.1‖ := norm_add_le _ _
      _ = |φ p.1| *‖F05BCFFun u.2.1 p‖ + |F05BCFFun u.1 p| *‖fderiv ℝ φ p.1‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ E*‖u‖ + ‖u‖*E := add_le_add
        (mul_le_mul h0 hG (norm_nonneg _) hE)
        (mul_le_mul hV h1 (norm_nonneg (fderiv ℝ φ p.1)) (norm_nonneg u))
      _ = _ := by ring
  have hHessian : ‖F05CutoffJetHessian φ u p‖ ≤ 4*E*‖u‖ := by
    unfold F05CutoffJetHessian
    calc
      _ ≤ ‖φ p.1 • F05BCFFun u.2.2.1.val.1 p‖ +
          ‖(fderiv ℝ φ p.1).smulRight (F05BCFFun u.2.1 p)‖ +
          ‖(F05BCFFun u.2.1 p).smulRight (fderiv ℝ φ p.1)‖ +
          ‖F05BCFFun u.1 p • fderiv ℝ (fderiv ℝ φ) p.1‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ = |φ p.1| *‖F05BCFFun u.2.2.1.val.1 p‖ +
          ‖fderiv ℝ φ p.1‖*‖F05BCFFun u.2.1 p‖ +
          ‖F05BCFFun u.2.1 p‖*‖fderiv ℝ φ p.1‖ +
          |F05BCFFun u.1 p| *‖fderiv ℝ (fderiv ℝ φ) p.1‖ := by
        simp only [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ E*‖u‖ + E*‖u‖ + ‖u‖*E + ‖u‖*E := by
        gcongr
      _ = _ := by ring
  exact ⟨hValue.trans (by nlinarith),hGradient.trans (by nlinarith),hHessian,hTime.trans (by nlinarith)⟩

theorem F05_cutoff_jet_raw_bound (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (Q : Set (Point n)) (u : F05JetComponent α Q) (p : Point n),
      |F05CutoffJetValue φ u p| ≤ C*‖u‖ ∧ ‖F05CutoffJetGradient φ u p‖ ≤ C*‖u‖ ∧
        ‖F05CutoffJetHessian φ u p‖ ≤ C*‖u‖ ∧ |F05CutoffJetTime φ u p| ≤ C*‖u‖ := by
  obtain ⟨E,hE,hBound⟩ := compact_cutoff_actual_jet_bound hφ hc
  refine ⟨4*E,by positivity,?_⟩
  intro α Q u p
  exact F05_cutoff_jet_raw_bound_of_bound hE.le φ hBound u p

end Yau.Proofs.F05Aux
