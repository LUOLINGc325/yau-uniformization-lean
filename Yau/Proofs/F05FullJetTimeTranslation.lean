import Yau.Proofs.F05RelativeFullJetHolder

/-! Complete actual four-jet Hölder tuples transport between arbitrary
closed slabs by a true time translation, with the fixed factor two. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_full_jet_holder_time_translation {X : Set (Space n)} {l r L R s α C : ℝ}
    (hlr : l < r) (hMap : MapsTo (fun t : ℝ => t+s) (Icc l r) (Icc L R))
    {u : Point n → ℝ} (hu : C2 (cylinder X L R) u)
    (hTuple : HolderBound α (cylinder X L R)
      (fun z => ((u z,spatialD u z),(spatialDD u z,timeD (cylinder X L R) u z))) C) :
    HolderBound α (cylinder X l r)
      (fun z => ((F05TimeAffine 1 s u z,spatialD (F05TimeAffine 1 s u) z),
        (spatialDD (F05TimeAffine 1 s u) z,timeD (cylinder X l r) (F05TimeAffine 1 s u) z))) (2*C) := by
  have hMap1 : MapsTo (fun t : ℝ => 1*t+s) (Icc l r) (Icc L R) := by
    simpa only [one_mul] using hMap
  have hh := F05_holder_timeAffine hMap1 hTuple
  have hActual : HolderBound α (cylinder X l r)
      (fun z => ((F05TimeAffine 1 s u z,spatialD (F05TimeAffine 1 s u) z),
        (spatialDD (F05TimeAffine 1 s u) z,timeD (cylinder X l r) (F05TimeAffine 1 s u) z)))
      (C*(1+|1|^(α/2))) := holderBound_congr_on hh (fun z hz => by
    refine Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl ?_)
    change timeD (cylinder X L R) u (F05TimeAffinePoint 1 s z) =
      timeD (cylinder X l r) (F05TimeAffine 1 s u) z
    simpa only [one_mul] using (F05_timeD_timeAffine hlr hMap1 hu hz).symm)
  convert! hActual using 1 <;> norm_num <;> ring

end Yau.Proofs.F05Aux
