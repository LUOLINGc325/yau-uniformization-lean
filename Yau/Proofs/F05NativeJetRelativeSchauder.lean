import Yau.Proofs.F05RelativeFullJetHolder

/-! Common actual native four-jet Hölder bounds give the literal relative
Schauder predicate on the same closed receiving cylinder. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_schauder_of_native_tuple {X : Set (Space n)} {l r α C : ℝ}
    (hX : UniqueDiffOn ℝ X) {u : Point n → ℝ} (hu : C2 (cylinder X l r) u)
    (hTuple : HolderBound α (cylinder X l r)
      (fun z => ((u z,spatialD u z),(spatialDD u z,timeD (cylinder X l r) u z))) C) :
    F05RelSchauder α X (Icc l r) u C := by
  have hD (z : Point n) (hz : z ∈ cylinder X l r) : F05RelD X u z = spatialD u z :=
    F05RelD_eq_spatialD (hX z.1 hz.1) ((hu.2.2.2.2.1 z hz).differentiableAt (by norm_num))
  have hDD (z : Point n) (hz : z ∈ cylinder X l r) : F05RelDD X u z = spatialDD u z :=
    F05RelDD_eq_spatialDD hX hz.1 (fun y hy => hu.2.2.2.2.1 (y,z.2) ⟨hy,hz.2⟩)
  refine ⟨F05_native_c2_to_relative hX hu,?_,?_,?_⟩
  · apply holderBound_congr_on (holderBound_fst hTuple)
    intro z hz
    change (u z,spatialD u z) = (u z,F05RelD X u z)
    rw [hD z hz]
  · exact holderBound_congr_on (holderBound_fst (holderBound_snd hTuple))
      (fun z hz => (hDD z hz).symm)
  · exact holderBound_congr_on (holderBound_snd (holderBound_snd hTuple))
      (fun z hz => (F05RelT_eq_timeD u hz.1).symm)

end Yau.Proofs.F05Aux
