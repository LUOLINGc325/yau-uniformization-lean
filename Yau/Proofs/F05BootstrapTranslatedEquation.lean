import Yau.Proofs.F05BootstrapRelativeTimeTranslation

/-! The complete relative operator commutes with translation of the time
slab and all actual coefficient fields. The spatial exterior set stays fixed. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_timeTranslate_operator {X : Set (Space n)} {l r τ : ℝ}
    (hlr : l < r) {u : Point n → ℝ} (hu : F05RelC2 X (Icc (l+τ) (r+τ)) u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    {z : Point n} (hz : z ∈ X ×ˢ Icc l r) :
    F05RelOp X (Icc l r) (timeTranslate τ a) (timeTranslate τ b) (timeTranslate τ u) z =
      F05RelOp X (Icc (l+τ) (r+τ)) a b u (timeTranslatePoint τ z) := by
  unfold F05RelOp
  rw [F05_relative_timeTranslate_time_jet hlr hu hz]
  rfl

theorem F05_translated_relative_equation {X : Set (Space n)} {l r τ : ℝ}
    (hlr : l < r) {u : Point n → ℝ} (hu : F05RelC2 X (Icc (l+τ) (r+τ)) u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f : Point n → ℝ)
    (hPDE : ∀ z ∈ X ×ˢ Icc (l+τ) (r+τ), F05RelOp X (Icc (l+τ) (r+τ)) a b u z = f z) :
    ∀ z ∈ X ×ˢ Icc l r,
      F05RelOp X (Icc l r) (timeTranslate τ a) (timeTranslate τ b) (timeTranslate τ u) z =
        timeTranslate τ f z := by
  intro z hz
  rw [F05_relative_timeTranslate_operator hlr hu a b hz]
  exact hPDE (timeTranslatePoint τ z) ⟨hz.1,add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩

theorem F05_timeTranslate_identity_exterior {X K : Set (Space n)} {l r τ : ℝ}
    {a : Point n → Mat n}
    (ha : ∀ z ∈ X ×ˢ Icc (l+τ) (r+τ), z.1 ∉ K → a z = 1) :
    ∀ z ∈ X ×ˢ Icc l r, z.1 ∉ K → timeTranslate τ a z = 1 := by
  intro z hz hzK
  exact ha (timeTranslatePoint τ z)
    ⟨hz.1,add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩ hzK

end Yau.Proofs.F05Aux
