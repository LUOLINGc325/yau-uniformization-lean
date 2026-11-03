import Yau.Proofs.F05RelativeLateBootstrap
import Yau.Proofs.F05BootstrapPositiveSmooth

/-! A genuine relative Schauder solution on one full raw late slab is
smooth on every strictly later receiving slab. The existing nonlinear
good-word bootstrap is applied after actual time translation, with the
empty physical face and zero smooth datum. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_late_interior_positive_smooth {l τ T α C K lam upper : ℝ}
    (hlτ : l < τ) (hτT : τ < T) (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C) (hK : 0 ≤ K)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R u : Point n → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Metric.ball 0 3 ×ˢ Icc l T))
    (hb : ∀ j, ContDiffOn ℝ ∞ (fun z => b z j) (Metric.ball 0 3 ×ˢ Icc l T))
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc l T))
    (he : Elliptic (region none (9/4) ×ˢ Icc l T) a lam upper)
    (hBound : ∀ z ∈ region none (9/4) ×ˢ Icc l T, |u z| ≤ K)
    (hu : F05RelSchauder α (region none (9/4)) (Icc l T) u C)
    (hEq : F05RelativeNonlinearEquation none (9/4) l T a b R u) :
    ContDiffOn ℝ ∞ u (region none (3/2) ×ˢ Icc τ T) := by
  let σ := (l+τ)/2
  let S := T-σ
  have hlσ : l < σ := by dsimp only [σ]; linarith
  have hστ : σ < τ := by dsimp only [σ]; linarith
  have hσT : σ < T := hστ.trans hτT
  have hS : 0 < S := by dsimp only [S]; linarith
  have hEnd : S+σ = T := by dsimp only [S]; ring
  have hSpace : region (n := n) none 2 ⊆ region none (9/4) := F05_region_mono (by norm_num)
  have hTime : Icc σ T ⊆ Icc l T := fun t ht => ⟨hlσ.le.trans ht.1,ht.2⟩
  have hSmall := F05_relative_schauder_restrict (F05_region_uniqueDiffOn none (by norm_num))
    (F05_region_uniqueDiffOn none (by norm_num)) (uniqueDiffOn_Icc hσT) hSpace hTime hu
  have hAligned : F05RelSchauder α (region none 2) (Icc (0+σ) (S+σ)) u C := by
    simpa only [zero_add,hEnd] using hSmall
  have hShift := F05_relative_schauder_timeTranslate hS hAligned
  have hLocal := F05_relative_closed_schauder_local none hC hShift
  have hSmallEq := F05_relative_nonlinear_equation_restrict none
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 9/4) (by norm_num) hσT hlσ.le le_rfl hu.1 hEq
  have hAlignedEq : F05RelativeNonlinearEquation none 2 (0+σ) (S+σ) a b R u := by
    simpa only [zero_add,hEnd] using hSmallEq
  have hShiftEq := F05_relative_nonlinear_time_translate none hS hAligned.1 hAlignedEq
  let Q : Set (Point n) := Metric.ball 0 3 ×ˢ Ioc 0 S
  have hEmb : ContDiffOn ℝ ∞ (timeTranslatePoint σ) Q :=
    (timeTranslatePoint_contDiff σ).contDiffOn
  have hMap : MapsTo (timeTranslatePoint σ) Q (Metric.ball 0 3 ×ˢ Icc l T) := by
    intro z hz
    refine ⟨hz.1,?_,?_⟩
    · change l ≤ z.2+σ
      linarith [hz.2.1]
    · change z.2+σ ≤ T
      linarith [hz.2.2]
  have haShift : ContDiffOn ℝ ∞ (timeTranslate σ a) Q := ha.comp hEmb hMap
  have hbShift (j : RIdx n) : ContDiffOn ℝ ∞
      (fun z => b (timeTranslatePoint σ z) j) Q := (hb j).comp hEmb hMap
  have hRShift : ContDiffOn ℝ ∞ (timeTranslate σ R) Q := hR.comp hEmb hMap
  have hPosSpace : F05PosSpace (n := n) none ⊆ region none 2 := fun x hx =>
    F05_posSpace_mem_region hx (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hx.2).le)
  have hPosMap (z : Point n) (hz : z ∈ F05PosPatch none S) :
      timeTranslatePoint σ z ∈ region none (9/4) ×ˢ Icc l T := by
    refine ⟨hSpace (hPosSpace hz.1),?_,?_⟩
    · change l ≤ z.2+σ
      linarith [hz.2.1]
    · change z.2+σ ≤ T
      linarith [hz.2.2]
  have hEllShift : Elliptic (F05PosPatch none S) (timeTranslate σ a) lam upper :=
    ⟨he.1,he.2.1,fun z hz => he.2.2 (timeTranslatePoint σ z) (hPosMap z hz)⟩
  have hBoundShift : ∀ z ∈ F05PosPatch none S, |timeTranslate σ u z| ≤ K :=
    fun z hz => hBound (timeTranslatePoint σ z) (hPosMap z hz)
  have hPosEq : ∀ z ∈ F05PosPatch none S,
      F05RelT (Ioc 0 S) (timeTranslate σ u) z = Real.exp (-timeTranslate σ u z)*
        ((∑ i,∑ j,timeTranslate σ a z i j*
            F05RelDD (F05PosSpace none) (timeTranslate σ u) z (realVec i) (realVec j))+
          ∑ i,b (timeTranslatePoint σ z) i*F05RelD (F05PosSpace none) (timeTranslate σ u) z (realVec i))+
        (1-Real.exp (-timeTranslate σ u z))*timeTranslate σ R z := by
    intro z hz
    have hJets := F05_relative_restriction_jets (F05_region_uniqueDiffOn none (by norm_num))
      (F05_posSpace_uniqueDiffOn none) (uniqueDiffOn_Ioc 0 S) hPosSpace Ioc_subset_Icc_self hShift.1 hz
    rw [hJets.1,hJets.2.1,hJets.2.2]
    exact hShiftEq z ⟨hPosSpace hz.1,Ioc_subset_Icc_self hz.2⟩
  have hθ : 0 < τ-σ := by linarith
  have hθS : τ-σ ≤ S := by dsimp only [S]; linarith
  have hSmooth := F05_flat_nonlinear_positive_cap_smooth
    hS hα hα1 hK (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (3/2 : ℝ) < 2) hθ hθS
    (timeTranslate σ a) (fun z j => b (timeTranslatePoint σ z) j) (timeTranslate σ R)
    (fun _ => 0) (timeTranslate σ u) haShift hbShift hRShift contDiffOn_const hLocal trivial hEllShift hBoundShift hPosEq
  let ψ : Point n → Point n := fun z => (z.1,z.2-σ)
  have hBackEmb : ContDiffOn ℝ ∞ ψ (region none (3/2) ×ˢ Icc τ T) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.sub contDiffOn_const)
  have hBackMap : MapsTo ψ (region none (3/2) ×ˢ Icc τ T)
      (region none (3/2) ×ˢ Icc (τ-σ) S) := by
    intro z hz
    refine ⟨hz.1,?_,?_⟩ <;> dsimp only [ψ,S] <;> linarith [hz.2.1,hz.2.2]
  have hComposite := hSmooth.comp hBackEmb hBackMap
  have hBackEq : (timeTranslate σ u) ∘ ψ = u := by
    funext z
    simp only [Function.comp_def,ψ,timeTranslate,timeTranslatePoint,sub_add_cancel,Prod.eta]
  rwa [hBackEq] at hComposite

end Yau.Proofs.F05Aux
