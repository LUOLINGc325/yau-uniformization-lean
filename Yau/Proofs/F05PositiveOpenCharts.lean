import Yau.Proofs.F05PositivePhysicalPatch
import Yau.Proofs.F05HolderGauge

/-! The proved closed positive-time smoothness yields actual joint
smoothness on the entire open physical chart, with no receiving-rim loss. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_positive_closed_to_open_charts {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (w : M.Carrier → ℝ → ℝ) {T : ℝ}
    (hFull : ∀ τ : ℝ, 0 < τ → τ < T → ∀ i,
      ContDiffOn ℝ ∞ (pull A i w) (F05D A i ×ˢ Icc τ T)) :
    ∀ i, ContDiffOn ℝ ∞ (pull A i w)
      ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T) := by
  intro i z hz
  let τ : ℝ := z.2/2
  have hτ : 0 < τ := by dsimp only [τ]; linarith [hz.2.1]
  have hτz : τ < z.2 := by dsimp only [τ]; linarith [hz.2.1]
  have hτT : τ < T := hτz.trans_le hz.2.2
  have hInner (j : Fin A.count) : ContDiffOn ℝ ∞ (pull A j w)
      (region (A.normal j) (3/2) ×ˢ Icc τ T) :=
    (hFull τ hτ hτT j).mono (prod_mono (F05_region_mono (by norm_num)) subset_rfl)
  have hSpace (x : Space n) (hx : x ∈ F05ModelOpen A i ∩ Metric.ball 0 3) :
      x ∈ {y | y ∈ Metric.ball 0 3 ∧ lift A i y ∈ closure O} := by
    refine ⟨hx.2,subset_closure ?_⟩
    apply (((hA.1 i).2.2.2.2.2.2.2 x hx.2).1).mpr
    have hModel := hx.1
    cases hν : A.normal i <;> simpa only [F05ModelOpen,hν,mem_ofPred_eq] using hModel
  have hAt := F05_inner_smooth_to_physical_patch hA w hInner i z ⟨hSpace z.1 hz.1,hτz.le,hz.2.2⟩
  apply hAt.mono_of_mem_nhdsWithin
  have hNear : {y : Point n | τ < y.2} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hτz
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hNear] with y hy hyTime
  exact ⟨hSpace y.1 hy.1,hyTime.le,hy.2.2⟩

end Yau.Proofs.F05Aux
