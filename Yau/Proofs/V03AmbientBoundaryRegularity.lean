import Yau.Proofs.V03ClearedBoundaryTensor
import Yau.Proofs.V03AmbientTensorRegularity
import Yau.Proofs.V03RectOperatorContinuity
import Yau.Proofs.V03TransitionInverse

/-! The original scaled boundary Hessian has a smooth ambient chart
representative and actual uniform operator bounds on each compact chart
piece times the entire closed physical-time and center-time slabs. -/

open scoped Topology ContDiff Matrix Manifold ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def fixedAmbientBoundaryTensor (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (p : (CotangentCoord n × ℝ) × ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  ambientLeviTensor (cotangentDG d.G x (cotangentChartInv x p.1.1))
    (clearedBoundaryTensor d j a x p)

theorem fixedAmbientBoundaryTensor_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (x : Pt X) (b c : Fin q) :
    ContDiffOn ℝ ∞ (fun p => fixedAmbientBoundaryTensor d j a x p b c)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) := by
  have hcoord : ContDiff ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ => p.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hA (k : Fin q) (i : CotangentIndex n) : ContDiffOn ℝ ∞
      (fun p : (CotangentCoord n × ℝ) × ℝ => cotangentDG d.G x (cotangentChartInv x p.1.1) k i)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) :=
    ((cotangentDG_chart_entry_contDiffOn hd.2.2.2.2.1.1 x k i).restrict_scalars ℝ).comp
      hcoord.contDiffOn (fun p hp => hp.1.1)
  have hdet : ∀ p : (CotangentCoord n × ℝ) × ℝ,
      p ∈ ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) →
      ((cotangentDG d.G x (cotangentChartInv x p.1.1))ᴴ *
        cotangentDG d.G x (cotangentChartInv x p.1.1)).det ≠ 0 := by
    intro p hp
    exact ne_of_gt (cotangentDG_gram_posDef_in_chart hd.2.2.2.2.1 x _
      (cotangentChartInv_mapsTo x hp.1.1)).det_pos
  exact ambientLeviTensor_entry_contDiffOn hA (clearedBoundaryTensor_entry_contDiffOn hd j a x) hdet b c

theorem fixedAmbientBoundaryTensor_compact_bound {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (x : Pt X) {C : Set (CotangentCoord n)}
    (hC : IsCompact C) (hCS : C ⊆ cotangentTarget x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ C, ∀ t ∈ Set.Icc 0 d.T, ∀ s ∈ Set.Icc 0 d.T,
      rectOpNorm (fixedAmbientBoundaryTensor d j a x ((z, t), s)) ≤ M := by
  have hcompact : IsCompact ((C ×ˢ Set.Icc 0 d.T) ×ˢ Set.Icc 0 d.T) :=
    (hC.prod isCompact_Icc).prod isCompact_Icc
  have hsub : ((C ×ˢ Set.Icc 0 d.T) ×ˢ Set.Icc 0 d.T) ⊆
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) := by
    intro p hp
    exact ⟨⟨hCS hp.1.1, ⟨hp.1.2.1, hp.1.2.2.trans hd.2.1.le⟩⟩, Set.mem_univ _⟩
  obtain ⟨M, hM, hbound⟩ := compact_rectOpNorm_bound hcompact
    (fun b c => (fixedAmbientBoundaryTensor_entry_contDiffOn hd j a x b c).continuousOn.mono hsub)
  exact ⟨M, hM, fun z hz t ht s hs => hbound ((z, t), s) ⟨⟨hz, ht⟩, hs⟩⟩

end Yau.Blueprint.V03Proof
