import Yau.Proofs.F05NativeRelativeBounds
import Yau.Proofs.F05BootstrapSchauderLimit
import Yau.Proofs.F05HolderTimeAffine

/-! The uniform relative estimates control the complete native jet tuple.
Its positive-time translation has a fixed bound before moving endpoints. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_full_jet_holder_of_relative {X : Set (Space n)} {l r α C : ℝ}
    (hX : UniqueDiffOn ℝ X) {u : Point n → ℝ} (hu : C2 (cylinder X l r) u)
    (hRel : F05RelSchauder α X (Icc l r) u C) :
    HolderBound α (cylinder X l r)
      (fun z => ((u z,spatialD u z),(spatialDD u z,timeD (cylinder X l r) u z))) C := by
  have hRaw := F05_holderBound_prod_same hRel.2.1
    (F05_holderBound_prod_same hRel.2.2.1 hRel.2.2.2)
  apply holderBound_congr_on hRaw
  intro z hz
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext ?_ (F05RelT_eq_timeD u hz.1))
  · exact F05RelD_eq_spatialD (hX z.1 hz.1) ((hu.2.2.2.2.1 z hz).differentiableAt (by norm_num))
  · exact F05RelDD_eq_spatialDD hX hz.1 (fun y hy => hu.2.2.2.2.1 (y,z.2) ⟨hy,hz.2⟩)

theorem F05_schauder_of_full_jet_holder {X : Set (Space n)} {l r α C : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder X l r) u)
    (hTuple : HolderBound α (cylinder X l r)
      (fun z => ((u z,spatialD u z),(spatialDD u z,timeD (cylinder X l r) u z))) C) :
    SchauderBound α (cylinder X l r) u C := by
  have hLow := holderBound_fst hTuple
  refine ⟨hu,hTuple.1,?_,holderBound_fst (holderBound_snd hTuple),
    holderBound_snd (holderBound_snd hTuple)⟩
  intro z hz
  have hPair := hLow.2.1 z hz
  change max ‖u z‖ ‖spatialD u z‖ ≤ C at hPair
  refine ⟨?_,(le_max_right ‖u z‖ ‖spatialD u z‖).trans hPair⟩
  simpa only [Real.norm_eq_abs] using (le_max_left ‖u z‖ ‖spatialD u z‖).trans hPair

theorem F05_full_jet_holder_time_shift {X : Set (Space n)} {l r T s α C : ℝ}
    (hT : 0 < T) (hMap : MapsTo (fun t : ℝ => t+s) (Icc 0 T) (Icc l r))
    {u : Point n → ℝ} (hu : C2 (cylinder X l r) u)
    (hTuple : HolderBound α (cylinder X l r)
      (fun z => ((u z,spatialD u z),(spatialDD u z,timeD (cylinder X l r) u z))) C) :
    HolderBound α (cylinder X 0 T)
      (fun z => ((F05TimeAffine 1 s u z,spatialD (F05TimeAffine 1 s u) z),
        (spatialDD (F05TimeAffine 1 s u) z,timeD (cylinder X 0 T) (F05TimeAffine 1 s u) z))) (2*C) := by
  have hMap1 : MapsTo (fun t : ℝ => 1*t+s) (Icc 0 T) (Icc l r) := by
    simpa only [one_mul] using hMap
  have hh := F05_holder_timeAffine hMap1 hTuple
  have hActual : HolderBound α (cylinder X 0 T)
      (fun z => ((F05TimeAffine 1 s u z,spatialD (F05TimeAffine 1 s u) z),
        (spatialDD (F05TimeAffine 1 s u) z,timeD (cylinder X 0 T) (F05TimeAffine 1 s u) z)))
      (C*(1+|1|^(α/2))) := holderBound_congr_on hh (fun z hz => by
    refine Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl ?_)
    change timeD (cylinder X l r) u (F05TimeAffinePoint 1 s z) =
      timeD (cylinder X 0 T) (F05TimeAffine 1 s u) z
    simpa only [one_mul] using (F05_timeD_timeAffine hT hMap1 hu hz).symm)
  convert! hActual using 1 <;> norm_num <;> ring

end Yau.Proofs.F05Aux
