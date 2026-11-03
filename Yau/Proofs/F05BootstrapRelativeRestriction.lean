import Yau.Proofs.F05BootstrapNative

/-! Restriction of computed one-sided jets uses uniqueness on the receiving
set. In particular no ambient spatial representative is required. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_restriction_jets {X Y : Set (Space n)} {I J : Set ℝ}
    {v : Point n → ℝ} (hX : UniqueDiffOn ℝ X) (hY : UniqueDiffOn ℝ Y)
    (hJ : UniqueDiffOn ℝ J) (hYX : Y ⊆ X) (hJI : J ⊆ I)
    (hv : F05RelC2 X I v) {z : Point n} (hz : z ∈ Y ×ˢ J) :
    F05RelD Y v z = F05RelD X v z ∧
      F05RelDD Y v z = F05RelDD X v z ∧ F05RelT J v z = F05RelT I v z := by
  have hD (w : Point n) (hw : w ∈ Y ×ˢ J) : F05RelD Y v w = F05RelD X v w :=
    fderivWithin_subset hYX (hY w.1 hw.1)
      ((hv.2.2.2.2.1 w.2 (hJI hw.2) w.1 (hYX hw.1)).differentiableWithinAt
        (by norm_num))
  refine ⟨hD z hz,?_,?_⟩
  · have hDiff : DifferentiableWithinAt ℝ (fun x => F05RelD X v (x,z.2)) X z.1 :=
      (((hv.2.2.2.2.1 z.2 (hJI hz.2)).fderivWithin hX (m := 1)
        (by norm_num)).differentiableOn (by norm_num)) z.1 (hYX hz.1)
    rw [F05RelDD,fderivWithin_congr
      (fun x hx => hD (x,z.2) ⟨hx,hz.2⟩) (hD z hz)]
    exact fderivWithin_subset hYX (hY z.1 hz.1) hDiff
  · exact derivWithin_subset hJI (hJ z.2 hz.2)
      (hv.2.2.2.2.2 z ⟨hYX hz.1,hJI hz.2⟩)

theorem F05_relative_c2_restrict {X Y : Set (Space n)} {I J : Set ℝ}
    {v : Point n → ℝ} (hX : UniqueDiffOn ℝ X) (hY : UniqueDiffOn ℝ Y)
    (hJ : UniqueDiffOn ℝ J) (hYX : Y ⊆ X) (hJI : J ⊆ I)
    (hv : F05RelC2 X I v) : F05RelC2 Y J v := by
  have hSub : Y ×ˢ J ⊆ X ×ˢ I := prod_mono hYX hJI
  have hEq (z : Point n) (hz : z ∈ Y ×ˢ J) :=
    F05_relative_restriction_jets hX hY hJ hYX hJI hv hz
  refine ⟨hv.1.mono hSub,(hv.2.1.mono hSub).congr (fun z hz => (hEq z hz).1),
    (hv.2.2.1.mono hSub).congr (fun z hz => (hEq z hz).2.1),
    (hv.2.2.2.1.mono hSub).congr (fun z hz => (hEq z hz).2.2),?_,?_⟩
  · intro t ht
    exact (hv.2.2.2.2.1 t (hJI ht)).mono hYX
  · intro z hz
    exact (hv.2.2.2.2.2 z (hSub hz)).mono hJI

theorem F05_relative_schauder_restrict {X Y : Set (Space n)} {I J : Set ℝ}
    {v : Point n → ℝ} {α C : ℝ} (hX : UniqueDiffOn ℝ X) (hY : UniqueDiffOn ℝ Y)
    (hJ : UniqueDiffOn ℝ J) (hYX : Y ⊆ X) (hJI : J ⊆ I)
    (hv : F05RelSchauder α X I v C) : F05RelSchauder α Y J v C := by
  have hSub : Y ×ˢ J ⊆ X ×ˢ I := prod_mono hYX hJI
  have hEq (z : Point n) (hz : z ∈ Y ×ˢ J) :=
    F05_relative_restriction_jets hX hY hJ hYX hJI hv.1 hz
  refine ⟨F05_relative_c2_restrict hX hY hJ hYX hJI hv.1,?_,?_,?_⟩
  · exact holderBound_congr_on (holderBound_mono hv.2.1 hSub)
      (fun z hz => by rw [(hEq z hz).1])
  · exact holderBound_congr_on (holderBound_mono hv.2.2.1 hSub)
      (fun z hz => (hEq z hz).2.1.symm)
  · exact holderBound_congr_on (holderBound_mono hv.2.2.2 hSub)
      (fun z hz => (hEq z hz).2.2.symm)

end Yau.Proofs.F05Aux
