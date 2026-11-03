import Yau.LeafProofs.L16HolderExtension
import Yau.LeafProofs.L16ChartCutoffBudget

/-! Fixed smooth compact spatial fields have Holder budgets before the
exponent and time interval are chosen. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_smooth_compact_spatial_holder {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Space n → V}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 →
      HolderBound α univ (fun p : Point n => g p.1) C := by
  obtain ⟨A,hA,hValue⟩ := compactSupport_continuous_norm_bound hg.continuous hc
  obtain ⟨D,hD,hDeriv⟩ := compactSupport_continuous_norm_bound
    (hg.continuous_fderiv (by simp)) (hc.fderiv ℝ)
  have hLip (x y : Space n) : ‖g x-g y‖ ≤ D*‖x-y‖ := by
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ)
      (fun z _ => hg.differentiable (by simp) z) (fun z _ => hDeriv z)
      convex_univ (mem_univ y) (mem_univ x)
  refine ⟨2*(A+D),by positivity,?_⟩
  intro α hα hα1
  exact spatial_bounded_lipschitz_holderBound_univ hα hα1 (by positivity)
    (fun x => (hValue x).trans (by linarith))
    (fun x y => (hLip x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))

theorem F05_smooth_cutoff_three_holder {n : ℕ} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 →
      HolderBound α univ (fun p : Point n => φ p.1) C ∧
      HolderBound α univ (fun p : Point n => fderiv ℝ φ p.1) C ∧
      HolderBound α univ (fun p : Point n => fderiv ℝ (fderiv ℝ φ) p.1) C := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ φ)) := hD.fderiv_right (by simp)
  obtain ⟨C₀,hC₀,h₀⟩ := F05_smooth_compact_spatial_holder hφ hc
  obtain ⟨C₁,hC₁,h₁⟩ := F05_smooth_compact_spatial_holder hD (hc.fderiv ℝ)
  obtain ⟨C₂,hC₂,h₂⟩ := F05_smooth_compact_spatial_holder hDD ((hc.fderiv ℝ).fderiv ℝ)
  refine ⟨C₀+C₁+C₂,by positivity,?_⟩
  intro α hα hα1
  exact ⟨holderBound_mono_const (h₀ α hα hα1) (by linarith),
    holderBound_mono_const (h₁ α hα hα1) (by linarith),
    holderBound_mono_const (h₂ α hα hα1) (by linarith)⟩

end Yau.Proofs.F05Aux
