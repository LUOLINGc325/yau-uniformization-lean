import Yau.Proofs.C02OpenCompositionJets

/-! Positive-order jets of an affine map depend only on its linear
part, so translations never enter the uniform chart constants. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affine_fderiv_eq (C : F) (S : E →L[ℝ] F) :
    fderiv ℝ (fun y => C + S y) = fun _ => S :=
  funext (fun _ => (S.hasFDerivAt.const_add C).fderiv)

theorem norm_iteratedFDeriv_affine_pos_le
    (C : F) (S : E →L[ℝ] F) (m : ℕ) (hm : 1 ≤ m) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => C + S y) x‖ ≤ ‖S‖ := by
  cases m with
  | zero => omega
  | succ m =>
    rw [← norm_iteratedFDeriv_fderiv, affine_fderiv_eq]
    cases m with
    | zero => simp only [norm_iteratedFDeriv_zero]; exact le_rfl
    | succ m => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using norm_nonneg S

end Yau.Blueprint.C02Proof
