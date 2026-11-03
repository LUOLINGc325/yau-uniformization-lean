import Yau.Proofs.F05BootstrapDefinitions

/-! Equality on the actual spatial-time product determines all computed
within derivatives. Values outside the product play no role. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_eqOn_jets {X : Set (Space n)} {I : Set ℝ}
    {f g : Point n → ℝ} (hEq : EqOn f g (X ×ˢ I)) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelD X f z = F05RelD X g z ∧ F05RelDD X f z = F05RelDD X g z ∧
      F05RelT I f z = F05RelT I g z := by
  have hD (w : Point n) (hw : w ∈ X ×ˢ I) : F05RelD X f w = F05RelD X g w :=
    fderivWithin_congr (fun x hx => hEq ⟨hx,hw.2⟩) (hEq hw)
  refine ⟨hD z hz,?_,?_⟩
  · exact fderivWithin_congr (fun x hx => hD (x,z.2) ⟨hx,hz.2⟩) (hD z hz)
  · exact derivWithin_congr (fun t ht => hEq ⟨hz.1,ht⟩) (hEq hz)

theorem F05_relative_schauder_congr {X : Set (Space n)} {I : Set ℝ}
    {f g : Point n → ℝ} {α C : ℝ} (hf : F05RelSchauder α X I f C)
    (hEq : EqOn f g (X ×ˢ I)) : F05RelSchauder α X I g C := by
  have hJets (z : Point n) (hz : z ∈ X ×ˢ I) := F05_relative_eqOn_jets hEq hz
  have hg : F05RelC2 X I g := by
    refine ⟨hf.1.1.congr (fun z hz => (hEq hz).symm),
      hf.1.2.1.congr (fun z hz => (hJets z hz).1.symm),
      hf.1.2.2.1.congr (fun z hz => (hJets z hz).2.1.symm),
      hf.1.2.2.2.1.congr (fun z hz => (hJets z hz).2.2.symm),?_,?_⟩
    · intro t ht
      exact (hf.1.2.2.2.2.1 t ht).congr (fun x hx => (hEq ⟨hx,ht⟩).symm)
    · intro z hz
      exact (hf.1.2.2.2.2.2 z hz).congr
        (fun t ht => (hEq (show ((z.1,t) : Point n) ∈ X ×ˢ I from ⟨hz.1,ht⟩)).symm)
        (hEq hz).symm
  refine ⟨hg,?_,?_,?_⟩
  · apply holderBound_congr_on hf.2.1
    intro z hz
    change (f z,F05RelD X f z) = (g z,F05RelD X g z)
    rw [hEq hz,(hJets z hz).1]
  · exact holderBound_congr_on hf.2.2.1 (fun z hz => (hJets z hz).2.1)
  · exact holderBound_congr_on hf.2.2.2 (fun z hz => (hJets z hz).2.2)

end Yau.Proofs.F05Aux
