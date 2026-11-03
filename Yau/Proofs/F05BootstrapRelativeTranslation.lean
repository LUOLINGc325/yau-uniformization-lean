import Yau.Proofs.F05BootstrapRelativeLinear
import Yau.LeafProofs.L16SpatialTransport

/-! Spatial translation transports the actual within spatial jets between
buffered physical sets. No ambient C2 extension or reflected equation enters. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_spatialTranslate_jets {X Y : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) (hY : UniqueDiffOn ℝ Y) (v : Space n)
    (hMap : MapsTo (fun x => x+v) X Y) {u : Point n → ℝ} (hu : F05RelC2 Y I u)
    {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelD X (spatialTranslate v u) z = F05RelD Y u (spatialTranslatePoint v z) ∧
      F05RelDD X (spatialTranslate v u) z = F05RelDD Y u (spatialTranslatePoint v z) ∧
      F05RelT I (spatialTranslate v u) z = F05RelT I u (spatialTranslatePoint v z) := by
  have hInner (x : Space n) : HasFDerivWithinAt (fun y => y+v)
      (ContinuousLinearMap.id ℝ (Space n)) X x := ((hasFDerivAt_id x).add_const v).hasFDerivWithinAt
  have hD (p : Point n) (hp : p ∈ X ×ˢ I) :
      F05RelD X (spatialTranslate v u) p = F05RelD Y u (spatialTranslatePoint v p) := by
    have h := ((hu.2.2.2.2.1 p.2 hp.2 (p.1+v) (hMap hp.1)).differentiableWithinAt
      (by norm_num)).hasFDerivWithinAt.comp p.1 (hInner p.1) hMap
    simpa only [F05RelD,spatialTranslate,spatialTranslatePoint,Function.comp_def,
      ContinuousLinearMap.comp_id] using h.fderivWithin (hX p.1 hp.1)
  refine ⟨hD z hz,?_,rfl⟩
  rw [F05RelDD,fderivWithin_congr (fun x hx => hD (x,z.2) ⟨hx,hz.2⟩) (hD z hz)]
  have hDiff := (((hu.2.2.2.2.1 z.2 hz.2).fderivWithin hY (m := 1)
    (by norm_num)).differentiableOn (by norm_num) (z.1+v) (hMap hz.1)).hasFDerivWithinAt
  have h := hDiff.comp z.1 (hInner z.1) hMap
  simpa only [F05RelDD,F05RelD,spatialTranslatePoint,Function.comp_def,
    ContinuousLinearMap.comp_id] using h.fderivWithin (hX z.1 hz.1)

theorem F05_relative_c2_spatialTranslate {X Y : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) (hY : UniqueDiffOn ℝ Y) (v : Space n)
    (hMap : MapsTo (fun x => x+v) X Y) {u : Point n → ℝ} (hu : F05RelC2 Y I u) :
    F05RelC2 X I (spatialTranslate v u) := by
  have hMaps : MapsTo (spatialTranslatePoint v) (X ×ˢ I) (Y ×ˢ I) := fun z hz => ⟨hMap hz.1,hz.2⟩
  have hContinuous : ContinuousOn (spatialTranslatePoint v) (X ×ˢ I) :=
    ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn
  have hJets (z : Point n) (hz : z ∈ X ×ˢ I) := F05_relative_spatialTranslate_jets hX hY v hMap hu hz
  refine ⟨hu.1.comp hContinuous hMaps,
    (hu.2.1.comp hContinuous hMaps).congr (fun z hz => (hJets z hz).1),
    (hu.2.2.1.comp hContinuous hMaps).congr (fun z hz => (hJets z hz).2.1),
    (hu.2.2.2.1.comp hContinuous hMaps).congr (fun z hz => (hJets z hz).2.2),?_,?_⟩
  · intro t ht
    exact (hu.2.2.2.2.1 t ht).comp (contDiff_id.add contDiff_const).contDiffOn hMap
  · intro z hz
    exact hu.2.2.2.2.2 (spatialTranslatePoint v z) (hMaps hz)

end Yau.Proofs.F05Aux
