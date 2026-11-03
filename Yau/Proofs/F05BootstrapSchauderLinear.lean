import Yau.Proofs.F05BootstrapOperatorLinear

/-! Actual relative Schauder fields are closed under addition and
subtraction, with their literal computed closed jets and summed budgets. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_sub_jets {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelC2 X I f) (hg : F05RelC2 X I g) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelD X (fun p => f p-g p) z = F05RelD X f z-F05RelD X g z ∧
      F05RelDD X (fun p => f p-g p) z = F05RelDD X f z-F05RelDD X g z ∧
      F05RelT I (fun p => f p-g p) z = F05RelT I f z-F05RelT I g z := by
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  have hAdd := F05_relative_add_jets hX hf (F05_relative_c2_const_mul hX hg (-1)) hz
  have hNeg := F05_relative_const_mul_jets hX hg (-1) hz
  rw [hNeg.1,hNeg.2.1,hNeg.2.2] at hAdd
  simpa only [neg_one_mul,neg_one_smul,sub_eq_add_neg] using hAdd

theorem F05_relative_schauder_add {X : Set (Space n)} {I : Set ℝ} {α C D : ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelSchauder α X I f C) (hg : F05RelSchauder α X I g D) :
    F05RelSchauder α X I (fun z => f z+g z) (C+D) := by
  have hJets := fun z hz => F05_relative_add_jets hX hf.1 hg.1 (z := z) hz
  refine ⟨F05_relative_c2_add hX hf.1 hg.1,?_,?_,?_⟩
  · apply holderBound_congr_on (holderBound_add hf.2.1 hg.2.1)
    intro z hz
    change (f z+g z,F05RelD X f z+F05RelD X g z) = (f z+g z,F05RelD X (fun p => f p+g p) z)
    rw [(hJets z hz).1]
  · exact holderBound_congr_on (holderBound_add hf.2.2.1 hg.2.2.1) (fun z hz => (hJets z hz).2.1.symm)
  · exact holderBound_congr_on (holderBound_add hf.2.2.2 hg.2.2.2) (fun z hz => (hJets z hz).2.2.symm)

theorem F05_relative_schauder_sub {X : Set (Space n)} {I : Set ℝ} {α C D : ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelSchauder α X I f C) (hg : F05RelSchauder α X I g D) :
    F05RelSchauder α X I (fun z => f z-g z) (C+D) := by
  have hJets := fun z hz => F05_relative_sub_jets hX hf.1 hg.1 (z := z) hz
  refine ⟨F05_relative_c2_sub hX hf.1 hg.1,?_,?_,?_⟩
  · apply holderBound_congr_on (holderBound_sub hf.2.1 hg.2.1)
    intro z hz
    change (f z-g z,F05RelD X f z-F05RelD X g z) = (f z-g z,F05RelD X (fun p => f p-g p) z)
    rw [(hJets z hz).1]
  · exact holderBound_congr_on (holderBound_sub hf.2.2.1 hg.2.2.1) (fun z hz => (hJets z hz).2.1.symm)
  · exact holderBound_congr_on (holderBound_sub hf.2.2.2 hg.2.2.2) (fun z hz => (hJets z hz).2.2.symm)

theorem F05_local_schauder_add {ν : Option (RIdx n)} {T α : ℝ} {f g : Point n → ℝ}
    (hf : F05LocalSchauder α ν T f) (hg : F05LocalSchauder α ν T g) :
    F05LocalSchauder α ν T (fun z => f z+g z) := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hF⟩ := hf r hr hr2 s hs hsT
  obtain ⟨D,hD,hG⟩ := hg r hr hr2 s hs hsT
  exact ⟨C+D,add_pos hC hD,F05_relative_schauder_add (F05_region_uniqueDiffOn ν hr) hF hG⟩

theorem F05_local_schauder_sub {ν : Option (RIdx n)} {T α : ℝ} {f g : Point n → ℝ}
    (hf : F05LocalSchauder α ν T f) (hg : F05LocalSchauder α ν T g) :
    F05LocalSchauder α ν T (fun z => f z-g z) := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hF⟩ := hf r hr hr2 s hs hsT
  obtain ⟨D,hD,hG⟩ := hg r hr hr2 s hs hsT
  exact ⟨C+D,add_pos hC hD,F05_relative_schauder_sub (F05_region_uniqueDiffOn ν hr) hF hG⟩

end Yau.Proofs.F05Aux
