import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Explicit finite Faà di Bruno difference bounds, including derivative order zero. -/

noncomputable section

open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

def taylorInnerDifferenceConstant (k : ℕ) (D : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition k, (c.length : ℝ) * D ^ (c.length - 1)

def taylorOuterDifferenceConstant (k : ℕ) (D : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition k, D ^ c.length

theorem taylorInnerDifferenceConstant_nonneg (k : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ taylorInnerDifferenceConstant k D :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))

theorem taylorOuterDifferenceConstant_nonneg (k : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ taylorOuterDifferenceConstant k D := Finset.sum_nonneg (fun _ _ => pow_nonneg hD _)

theorem norm_taylorComp_sub_le
    (p₁ p₂ : FormalMultilinearSeries ℝ F G) (q₁ q₂ : FormalMultilinearSeries ℝ E F)
    (k : ℕ) {A B D Q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hp₁ : ∀ j, j ≤ k → ‖p₁ j‖ ≤ A)
    (hpΔ : ∀ j, j ≤ k → ‖p₁ j - p₂ j‖ ≤ B)
    (hq₁ : ∀ j, j ≤ k → ‖q₁ j‖ ≤ D)
    (hq₂ : ∀ j, j ≤ k → ‖q₂ j‖ ≤ D)
    (hqΔ : ∀ j, j ≤ k → ‖q₁ j - q₂ j‖ ≤ Q) :
    ‖p₁.taylorComp q₁ k - p₂.taylorComp q₂ k‖ ≤
      taylorInnerDifferenceConstant k D * A * Q + taylorOuterDifferenceConstant k D * B := by
  have hterm (c : OrderedFinpartition k) :
      ‖p₁.compAlongOrderedFinpartition q₁ c - p₂.compAlongOrderedFinpartition q₂ c‖ ≤
        A * c.length * D ^ (c.length - 1) * Q + B * D ^ c.length := by
    let g₁ : ∀ i : Fin c.length, E [×c.partSize i]→L[ℝ] F := fun i => q₁ (c.partSize i)
    let g₂ : ∀ i : Fin c.length, E [×c.partSize i]→L[ℝ] F := fun i => q₂ (c.partSize i)
    have hg₁ : ‖g₁‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr
      (fun i => hq₁ _ (c.partSize_le i))
    have hg₂ : ‖g₂‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr
      (fun i => hq₂ _ (c.partSize_le i))
    have hgΔ : ‖g₁ - g₂‖ ≤ Q := (pi_norm_le_iff_of_nonneg hQ).mpr
      (fun i => hqΔ _ (c.partSize_le i))
    have hgmax : max ‖g₁‖ ‖g₂‖ ≤ D := max_le hg₁ hg₂
    have hprod : ∏ i : Fin c.length, ‖g₂ i‖ ≤ D ^ c.length := by
      calc
        _ ≤ ∏ _ : Fin c.length, D := Finset.prod_le_prod₀
          (fun _ _ => norm_nonneg _) (fun i _ => hq₂ _ (c.partSize_le i))
        _ = _ := by simp
    have hfirst : ‖p₁ c.length‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ ≤
        A * c.length * D ^ (c.length - 1) * Q := by
      gcongr
      · exact hp₁ _ c.length_le
    have hsecond : ‖p₁ c.length - p₂ c.length‖ * (∏ i, ‖g₂ i‖) ≤ B * D ^ c.length :=
      mul_le_mul (hpΔ _ c.length_le) hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hB
    exact (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
      (p₁ c.length) (p₂ c.length) g₁ g₂).trans (add_le_add hfirst hsecond)
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c : OrderedFinpartition k,
        ‖p₁.compAlongOrderedFinpartition q₁ c - p₂.compAlongOrderedFinpartition q₂ c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition k,
        (A * c.length * D ^ (c.length - 1) * Q + B * D ^ c.length) :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = _ := by
      simp only [Finset.sum_add_distrib, taylorInnerDifferenceConstant,
        taylorOuterDifferenceConstant, Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro c _ <;> ring


/-- The explicit difference estimate applies to the actual iterated derivatives,
with distinct source points and distinct outer functions. -/
theorem norm_iteratedFDeriv_comp_sub_le
    {f₁ f₂ : E → F} {g₁ g₂ : F → G} {x y : E} (k : ℕ)
    (hg₁ : ContDiffAt ℝ (k : ℕ∞ω) g₁ (f₁ x))
    (hg₂ : ContDiffAt ℝ (k : ℕ∞ω) g₂ (f₂ y))
    (hf₁ : ContDiffAt ℝ (k : ℕ∞ω) f₁ x)
    (hf₂ : ContDiffAt ℝ (k : ℕ∞ω) f₂ y)
    {A B D Q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hp₁ : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g₁ (f₁ x)‖ ≤ A)
    (hpΔ : ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j g₁ (f₁ x) - iteratedFDeriv ℝ j g₂ (f₂ y)‖ ≤ B)
    (hq₁ : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f₁ x‖ ≤ D)
    (hq₂ : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f₂ y‖ ≤ D)
    (hqΔ : ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j f₁ x - iteratedFDeriv ℝ j f₂ y‖ ≤ Q) :
    ‖iteratedFDeriv ℝ k (g₁ ∘ f₁) x - iteratedFDeriv ℝ k (g₂ ∘ f₂) y‖ ≤
      taylorInnerDifferenceConstant k D * A * Q + taylorOuterDifferenceConstant k D * B := by
  rw [iteratedFDeriv_comp hg₁ hf₁ (by simp : k ≤ (k : ℕ∞ω)),
    iteratedFDeriv_comp hg₂ hf₂ (by simp : k ≤ (k : ℕ∞ω))]
  exact norm_taylorComp_sub_le (ftaylorSeries ℝ g₁ (f₁ x)) (ftaylorSeries ℝ g₂ (f₂ y))
    (ftaylorSeries ℝ f₁ x) (ftaylorSeries ℝ f₂ y) k hA hB hD hQ hp₁ hpΔ hq₁ hq₂ hqΔ

end Yau.LeafProofs.L17Aux
