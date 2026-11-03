import Yau.Proofs.F05BootstrapRelativeMultiplication
import Yau.Proofs.F05BootstrapStationary

/-! Linear operations on actual relative jets, retaining their computed
closed spatial and one-sided time derivatives. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_add_jets {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelC2 X I f) (hg : F05RelC2 X I g) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelD X (fun z => f z+g z) z = F05RelD X f z+F05RelD X g z ∧
      F05RelDD X (fun z => f z+g z) z = F05RelDD X f z+F05RelDD X g z ∧
      F05RelT I (fun z => f z+g z) z = F05RelT I f z+F05RelT I g z := by
  have hD (p : Point n) (hp : p ∈ X ×ˢ I) :
      F05RelD X (fun z => f z+g z) p = F05RelD X f p+F05RelD X g p :=
    fderivWithin_fun_add (hX p.1 hp.1)
      ((hf.2.2.2.2.1 p.2 hp.2 p.1 hp.1).differentiableWithinAt (by norm_num))
      ((hg.2.2.2.2.1 p.2 hp.2 p.1 hp.1).differentiableWithinAt (by norm_num))
  refine ⟨hD z hz,?_,derivWithin_fun_add (hf.2.2.2.2.2 z hz) (hg.2.2.2.2.2 z hz)⟩
  rw [F05RelDD,fderivWithin_congr (fun x hx => hD (x,z.2) ⟨hx,hz.2⟩) (hD z hz)]
  exact fderivWithin_fun_add (hX z.1 hz.1)
    (((hf.2.2.2.2.1 z.2 hz.2).fderivWithin hX (m := 1) (by norm_num)).differentiableOn (by norm_num) z.1 hz.1)
    (((hg.2.2.2.2.1 z.2 hz.2).fderivWithin hX (m := 1) (by norm_num)).differentiableOn (by norm_num) z.1 hz.1)

theorem F05_relative_c2_add {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelC2 X I f) (hg : F05RelC2 X I g) :
    F05RelC2 X I (fun z => f z+g z) := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  refine ⟨hf.1.add hg.1,(hf.2.1.add hg.2.1).congr (fun z hz => (F05_relative_add_jets hX hf hg hz).1),
    (hf.2.2.1.add hg.2.2.1).congr (fun z hz => (F05_relative_add_jets hX hf hg hz).2.1),
    (hf.2.2.2.1.add hg.2.2.2.1).congr (fun z hz => (F05_relative_add_jets hX hf hg hz).2.2),?_,?_⟩
  · intro t ht
    exact (hf.2.2.2.2.1 t ht).add (hg.2.2.2.2.1 t ht)
  · intro z hz
    exact (hf.2.2.2.2.2 z hz).add (hg.2.2.2.2.2 z hz)

theorem F05_relative_c2_const_mul {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f : Point n → ℝ} (hf : F05RelC2 X I f) (c : ℝ) :
    F05RelC2 X I (fun z => c*f z) :=
  F05_relative_c2_mul hX (F05_relative_spatial_profile hX (φ := fun _ => c) contDiff_const) hf

theorem F05_relative_c2_sub {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelC2 X I f) (hg : F05RelC2 X I g) :
    F05RelC2 X I (fun z => f z-g z) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using
    F05_relative_c2_add hX hf (F05_relative_c2_const_mul hX hg (-1))

end Yau.Proofs.F05Aux
