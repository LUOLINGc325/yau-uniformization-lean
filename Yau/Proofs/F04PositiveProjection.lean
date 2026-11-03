import Yau.Proofs.F04PositiveIndicator

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- The strict active-set multiplier is an actual idempotent on the completed
form space, proved using its genuine L2 section representatives. -/
theorem positiveFormMultiplier_idempotent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : Lp ℝ 2 μ) (a : L2FormHilbert g μ k) :
    positiveFormMultiplier g μ f (positiveFormMultiplier g μ f a) = positiveFormMultiplier g μ f a := by
  obtain ⟨A, hA, hrep⟩ := l2FormHilbert_exists_section g μ a
  let Ap : RealForm M k := fun x => if 0 < f x then A x else 0
  have hAp : L2RealForm g.form μ Ap := positive_active_form_l2 g μ f A hA
  have hMa : positiveFormMultiplier g μ f a = realizeL2Form g μ (L2FormSpace.ofSection Ap hAp) := by
    rw [← hrep, positiveFormMultiplier_realize]
  have hMap : positiveFormMultiplier g μ f (realizeL2Form g μ (L2FormSpace.ofSection Ap hAp)) =
      realizeL2Form g μ (L2FormSpace.ofSection Ap hAp) := by
    rw [positiveFormMultiplier_realize]
    apply (realizeL2Form_eq_iff_ae g μ _ _).mpr
    apply ae_of_all
    intro x
    change (if 0 < f x then Ap x else 0) = Ap x
    dsimp only [Ap]
    split_ifs <;> rfl
  rw [hMa, hMap]

/-- The genuine active differential supplies the exact fixed-metric Green
pairing required by the coercive shifted barrier test. -/
theorem positiveFormMultiplier_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : Lp ℝ 2 μ) (a : L2FormHilbert g μ k) :
    inner ℝ a (positiveFormMultiplier g μ f a) = ‖positiveFormMultiplier g μ f a‖ ^ 2 := by
  have hs := multiplyL2FormHilbert_inner_symm g μ (fun x => positiveIndicator (f x))
    (positiveIndicator_aestronglyMeasurable μ f) 1 zero_le_one
    (fun x => positiveIndicator_abs_le (f x)) a (positiveFormMultiplier g μ f a)
  change inner ℝ (positiveFormMultiplier g μ f a) (positiveFormMultiplier g μ f a) =
    inner ℝ a (positiveFormMultiplier g μ f (positiveFormMultiplier g μ f a)) at hs
  rw [positiveFormMultiplier_idempotent] at hs
  exact hs.symm.trans (real_inner_self_eq_norm_sq _)

/-- The same strict indicator identity works for arbitrary coefficient
bilinear forms, before any integration or metric comparison. -/
theorem bilinear_indicator_right {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : Prop) [Decidable p] (a b : E) :
    B a (if p then b else 0) = B (if p then a else 0) (if p then b else 0) := by
  by_cases h : p
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h, map_zero]

end Yau.F04Proof
