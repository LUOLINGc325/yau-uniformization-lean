import Yau.Proofs.F05CrossAtlasSmooth
import Yau.Proofs.F05SmoothTimeTranslation

/-! Once a fixed full raw chart lies in a later solution domain, the
proved positive-time boundary bootstrap supplies its actual smooth
closed-slab pull and its genuine positive time translation. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_cross_atlas_raw_positive_smooth {O V : Set M.Carrier} {A B : AtlasData M}
    (hA : GenuineAtlas O A) (hB : GenuineAtlas V B) (w : M.Carrier → ℝ → ℝ)
    {s T : ℝ} (hs : 0 < s) (hsT : s < T) (i : Fin A.count)
    (hDomain : lift A i '' Metric.ball 0 3 ⊆ closure V)
    (hFull : ∀ τ : ℝ, 0 < τ → τ < T → ∀ j,
      ContDiffOn ℝ ∞ (pull B j w) (F05D B j ×ˢ Icc τ T)) :
    ContDiffOn ℝ ∞ (pull A i w) (Metric.ball 0 3 ×ˢ Icc s T) := by
  have hInner (j : Fin B.count) : ContDiffOn ℝ ∞ (pull B j w)
      (region (B.normal j) (3/2) ×ˢ Icc s T) :=
    (hFull s hs hsT j).mono
      (prod_mono (F05_region_mono (by norm_num : (3/2 : ℝ) ≤ 2)) subset_rfl)
  exact (F05_cross_atlas_positive_smooth hA hB w hInner i).mono
    (fun z hz => ⟨⟨hz.1,hDomain ⟨z.1,hz.1,rfl⟩⟩,hz.2⟩)

theorem F05_cross_atlas_raw_shift_smooth {O V : Set M.Carrier} {A B : AtlasData M}
    (hA : GenuineAtlas O A) (hB : GenuineAtlas V B) (w : M.Carrier → ℝ → ℝ)
    {s T : ℝ} (hs : 0 < s) (hsT : s < T) (i : Fin A.count)
    (hDomain : lift A i '' Metric.ball 0 3 ⊆ closure V)
    (hFull : ∀ τ : ℝ, 0 < τ → τ < T → ∀ j,
      ContDiffOn ℝ ∞ (pull B j w) (F05D B j ×ˢ Icc τ T)) :
    ContDiffOn ℝ ∞ (pull A i (F05ManifoldTimeShift s w))
      (Metric.ball 0 3 ×ˢ Icc 0 (T-s)) := by
  have hRaw := F05_cross_atlas_raw_positive_smooth hA hB w hs hsT i hDomain hFull
  have hEmb : ContDiffOn ℝ ∞ (fun z : Point n => (z.1,z.2+s))
      (Metric.ball 0 3 ×ˢ Icc 0 (T-s)) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const)
  have hMap : MapsTo (fun z : Point n => (z.1,z.2+s))
      (Metric.ball 0 3 ×ˢ Icc 0 (T-s)) (Metric.ball 0 3 ×ˢ Icc s T) := by
    intro z hz
    refine ⟨hz.1,?_,?_⟩ <;> linarith [hz.2.1,hz.2.2]
  exact hRaw.comp hEmb hMap

end Yau.Proofs.F05Aux
