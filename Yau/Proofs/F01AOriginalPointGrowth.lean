import Yau.Proofs.F01ASmoothComparison

/-! The original pointwise growth quantifiers follow from the same canonical
comparison. The section and its comparison coefficient are fixed at x before
the time variable is introduced. The historical e266669 source is unavailable
in this checkout; this proof uses only the published comparison interface. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Proofs.P04Aux
variable {n : ℕ}

theorem original_point_growth_of_canonical_bound
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (P ρ : STF X)
    {η : ℝ} (hη : 0 < η) (hcanonical : CanonicalRhoPointBound X o u P η)
    (hsections : CanonicalInitialData X o)
    (hρ : ∀ x t, 0 ≤ t → ρ x t = -P x t) :
    ∀ x, ∃ C : ℝ, ∀ t, 0 ≤ t → ρ x t ≤ C * (1 + t) := by
  intro x
  obtain ⟨S, hS, hxS, hgrowth⟩ := hsections.1 x
  obtain ⟨a, ha, hbound⟩ := hcanonical S hS hgrowth
  let κ : ℝ := η / 3
  have hκ : 0 < κ := div_pos hη (by norm_num)
  let B : ℝ := |Real.log (canonicalNormSq X.metric.form S x)| + κ * u x ^ 2 +
    a + a / κ + (n : ℝ)
  refine ⟨2 * B, ?_⟩
  intro t ht
  let D : ℝ := 2 * (1 + t)
  let ε : ℝ := κ / (1 + t)
  have htime : 0 < 1 + t := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hε : 0 < ε := div_pos hκ htime
  have hεadm : ε ≤ η / (D + 1) := by
    apply (div_le_div_iff₀ htime (by dsimp [D]; positivity)).mpr
    dsimp [D, κ]
    nlinarith
  have htD : t ∈ Icc 0 (D / 2) := by
    constructor
    · exact ht
    · dsimp [D]; linarith
  have hxq : 0 < canonicalNormSq X.metric.form S x :=
    lt_of_le_of_ne (canonicalNormSq_nonneg _ _ _)
      (Ne.symm ((canonicalNormSq_eq_zero_iff _ _ _).not.mpr hxS))
  have hb := hbound D hD ε hε hεadm x t htD hxq
  have hεle : ε ≤ κ := by
    apply (div_le_iff₀ htime).mpr
    nlinarith
  have hinv : ε⁻¹ = (1 + t) / κ := by
    dsimp [ε]
    rw [inv_div]
  have hsquare := mul_le_mul_of_nonneg_right hεle (sq_nonneg (u x))
  have hconstant : 0 ≤ |Real.log (canonicalNormSq X.metric.form S x)| +
      κ * u x ^ 2 + a + (n : ℝ) := by positivity
  have hlinear : 2 * (|Real.log (canonicalNormSq X.metric.form S x)| +
      ε * u x ^ 2 + a * (1 + ε⁻¹) + (n : ℝ)) ≤ (2 * B) * (1 + t) := by
    rw [hinv]
    dsimp [B]
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg ht hconstant]
  rw [hρ x t ht]
  exact hb.trans hlinear

end Yau.NodeProofs.F01Aux
