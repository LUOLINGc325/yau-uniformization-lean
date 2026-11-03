import Yau.Proofs.F01HolderComposition
import Yau.Proofs.F01CompactJets

/-! A genuine smooth map on a neighborhood of a compact convex matrix
range has one numerical Holder composition budget before every realized
coefficient function. Actual derivative bounds and the mean value estimate
provide the Lipschitz constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_convex_smooth_lipschitz {K U : Set E} {φ : E → F}
    (hU : IsOpen U) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) :
    ∃ M L : ℝ, 0 < M ∧ 0 < L ∧ (∀ x ∈ K, ‖φ x‖ ≤ M) ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖φ x - φ y‖ ≤ L * ‖x - y‖) := by
  obtain ⟨C, hC, hc⟩ := compact_all_derivative_budgets hU hK hKU hφ
  refine ⟨C 0, C 1, hC 0, hC 1, ?_, ?_⟩
  · intro x hx
    simpa only [norm_iteratedFDeriv_zero] using hc 0 x hx
  · intro x hx y hy
    apply Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hφ.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp))
      (fun z hz => ?_) hConv hy hx
    simpa only [norm_iteratedFDeriv_one] using hc 1 z hz

theorem compact_smooth_holder_composition_budget {K U : Set E} {φ : E → F} {C : ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (β : ℝ) (f : Point n → E),
      HolderBound β Q f C → MapsTo f Q K → HolderBound β Q (fun p => φ (f p)) B := by
  obtain ⟨M, L, hM, hL, hs, hl⟩ := compact_convex_smooth_lipschitz hU hK hConv hKU hφ
  exact holder_lipschitz_composition_budget hM.le hL.le hC hs hl

end Yau.NodeProofs.F01Aux
