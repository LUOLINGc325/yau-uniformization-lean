import Yau.Proofs.V03BoundaryTensorTransport
import Yau.Proofs.V03BoundaryHermitian

/-! The original symbol has one uniform operator bound before every
admissible disc and normalized frame. The finite native chart compactness
comes from VariationSetup itself; no extra compactness or rank is assumed. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundarySymbol_uniform_opNorm {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian ∧
        rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤ M := by
  classical
  have hK : CotangentCompact (boundaryCompact d j) :=
    (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.1
  obtain ⟨m, x, C, hC, hcover⟩ := hK
  have hpieces : ∀ i : Fin m, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ C i, ∀ t ∈ Set.Icc 0 d.T, ∀ s ∈ Set.Icc 0 d.T,
        rectOpNorm (fixedAmbientBoundaryTensor d j a (x i) ((z, t), s)) ≤ M :=
    fun i => fixedAmbientBoundaryTensor_compact_bound hd j a (x i) (hC i).1 (hC i).2
  choose M hM hbound using hpieces
  refine ⟨∑ i, M i, Finset.sum_nonneg (fun i _ => hM i), ?_⟩
  intro F E hF hE θ
  refine ⟨boundarySymbol_isHermitian hd hF a E θ, ?_⟩
  let y := F.f (circlePoint θ)
  have hregion : y ∈ boundaryRegion d j := hF.2.2.2.2.2.2.2.1 θ
  have hyK : y ∈ boundaryCompact d j := ⟨hregion.1.le, hregion.2.le⟩
  rw [hcover] at hyK
  obtain ⟨i, z, hz, hzy⟩ := Set.mem_iUnion.mp hyK
  have hzTarget : z ∈ cotangentTarget (x i) := (hC i).2 hz
  have hySource : y ∈ cotangentSource (x i) := by
    rw [← hzy]
    exact cotangentChartInv_mapsTo (x i) hzTarget
  have hyChart : cotangentChart (x i) y = z := by
    rw [← hzy]
    exact cotangentChart_right_inv (x i) hzTarget
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have hs : F.s ∈ Set.Icc 0 d.T := ⟨hF.2.2.2.1.le, hF.2.2.2.2.1.le⟩
  have hb := hbound i z hz (discTime F (circlePoint θ)) ⟨ht.1.le, ht.2.le⟩ F.s hs
  have hn := boundarySymbol_opNorm_le_fixedAmbient hd j a ha F hF E hE θ (x i) hySource
  change rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤ _ at hn
  rw [show cotangentChart (x i) (F.f (circlePoint θ)) = z from hyChart] at hn
  exact (hn.trans hb).trans (Finset.single_le_sum (fun k _ => hM k) (Finset.mem_univ i))

end Yau.Blueprint.V03Proof
