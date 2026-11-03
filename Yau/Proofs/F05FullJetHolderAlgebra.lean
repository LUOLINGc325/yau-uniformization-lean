import Yau.Proofs.F05RelativeFullJetHolder
import Yau.Proofs.F05SchauderLinear

/-! Restriction and subtraction retain a bound for the actual complete
parabolic jet, including the low value/gradient Hölder seminorm. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_full_jet_holder_restrict_interval {X : Set (Space n)} {l r L R α C : ℝ}
    (hlr : l < r) (hLl : L ≤ l) (hrR : r ≤ R) {u : Point n → ℝ}
    (hu : C2 (cylinder X L R) u)
    (hTuple : HolderBound α (cylinder X L R)
      (fun z => ((u z,spatialD u z),(spatialDD u z,timeD (cylinder X L R) u z))) C) :
    HolderBound α (cylinder X l r)
      (fun z => ((u z,spatialD u z),(spatialDD u z,timeD (cylinder X l r) u z))) C := by
  have hSub : cylinder X l r ⊆ cylinder X L R :=
    fun z hz => ⟨hz.1,hLl.trans hz.2.1,hz.2.2.trans hrR⟩
  apply holderBound_congr_on (holderBound_mono hTuple hSub)
  intro z hz
  exact Prod.ext rfl (Prod.ext rfl (F05_timeD_restrict_interval hlr hLl hrR hu hz).symm)

theorem F05_full_jet_holder_sub {Q : Set (Point n)} {α C D : ℝ} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v)
    (hU : HolderBound α Q (fun z => ((u z,spatialD u z),(spatialDD u z,timeD Q u z))) C)
    (hV : HolderBound α Q (fun z => ((v z,spatialD v z),(spatialDD v z,timeD Q v z))) D) :
    HolderBound α Q
      (fun z => (((u z-v z),spatialD (fun p => u p-v p) z),
        (spatialDD (fun p => u p-v p) z,timeD Q (fun p => u p-v p) z))) (C+D) := by
  apply holderBound_congr_on (holderBound_sub hU hV)
  intro z hz
  exact Prod.ext (Prod.ext rfl (spatialD_sub hu hv hz).symm)
    (Prod.ext (spatialDD_sub hu hv hz).symm (timeD_sub hu hv hz).symm)

end Yau.Proofs.F05Aux
