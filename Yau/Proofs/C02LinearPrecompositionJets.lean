import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Jet bounds under a linear change of source coordinates on an actual
open smooth domain. No infinite-order germ is promoted to a neighborhood. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_comp_linearOn_le (L : D →L[ℝ] E)
    {O : Set E} (hO : IsOpen O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O)
    (x : D) (hx : L x ∈ O) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ * ‖L‖ ^ m := by
  have hPre : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right hf hO.uniqueDiffOn hPre.uniqueDiffOn hx
    (show (m : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_of_isOpen m hPre hx,
    iteratedFDerivWithin_of_isOpen m hO hx] at heq
  rw [heq]
  exact ((iteratedFDeriv ℝ m f (L x)).norm_compContinuousLinearMap_le (fun _ => L)).trans_eq
    (by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin])

theorem norm_iteratedFDeriv_comp_smulOn_le {O : Set E} (hO : IsOpen O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (a : ℝ) (x : E) (hx : a • x ∈ O) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f (a • y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (a • x)‖ * |a| ^ m := by
  let L : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ |a| := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)) (abs_nonneg a)
  exact (norm_iteratedFDeriv_comp_linearOn_le L hO hf x hx m).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL m) (norm_nonneg _))

end Yau.Blueprint.C02Proof
