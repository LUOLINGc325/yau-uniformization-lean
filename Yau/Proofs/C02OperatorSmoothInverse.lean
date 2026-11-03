import Yau.Proofs.C02OperatorInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The computed inverse is the library's actual inverse operation, with a
uniform bound and smooth dependence at every point of the fixed domain. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem isInvertible_of_close_identity (B : E →L[ℝ] E)
    (hB : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) : B.IsInvertible := by
  obtain ⟨V, hVB, hBV, _⟩ := exists_bounded_inverse_of_close_identity B hB
  exact ContinuousLinearMap.IsInvertible.of_inverse hBV hVB

theorem norm_actual_inverse_of_close_identity (B : E →L[ℝ] E)
    (hB : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) : ‖B.inverse‖ ≤ 2 := by
  obtain ⟨V, hVB, hBV, hV⟩ := exists_bounded_inverse_of_close_identity B hB
  rw [ContinuousLinearMap.inverse_eq hBV hVB]
  exact hV

theorem actual_inverse_identities_of_close_identity (B : E →L[ℝ] E)
    (hB : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    B.inverse.comp B = ContinuousLinearMap.id ℝ E ∧
      B.comp B.inverse = ContinuousLinearMap.id ℝ E := by
  have hInv := isInvertible_of_close_identity B hB
  exact ⟨hInv.inverse_comp_self, hInv.self_comp_inverse⟩

theorem contDiffOn_actual_inverse_of_close_identity
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {O : Set D} {B : D → E →L[ℝ] E} (hSmooth : ContDiffOn ℝ ∞ B O)
    (hClose : ∀ x ∈ O, ‖B x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ContDiffOn ℝ ∞ (fun x => (B x).inverse) O := by
  intro x hx
  exact ((isInvertible_of_close_identity (B x) (hClose x hx)).contDiffAt_map_inverse
    (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt x (hSmooth x hx)

end Yau.Blueprint.C02Proof
