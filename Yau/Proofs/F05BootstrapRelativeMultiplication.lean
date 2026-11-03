import Yau.Proofs.F05BootstrapRelativeProduct

/-! Relative parabolic C2 fields are closed under multiplication, with
continuous computed spatial Hessians and one-sided time derivatives. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_c2_mul {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelC2 X I f) (hg : F05RelC2 X I g) :
    F05RelC2 X I (fun z => f z*g z) := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  have hD (z : Point n) (hz : z ∈ X ×ˢ I) :
      F05RelD X (fun z => f z*g z) z =
        f z • F05RelD X g z+g z • F05RelD X f z :=
    fderivWithin_fun_mul (hX z.1 hz.1)
      ((hf.2.2.2.2.1 z.2 hz.2 z.1 hz.1).differentiableWithinAt (by norm_num))
      ((hg.2.2.2.2.1 z.2 hz.2 z.1 hz.1).differentiableWithinAt (by norm_num))
  have hH (z : Point n) (hz : z ∈ X ×ˢ I) :
      F05RelDD X (fun z => f z*g z) z =
        f z • F05RelDD X g z+
          (F05RelD X f z).smulRight (F05RelD X g z)+
          (F05RelD X g z).smulRight (F05RelD X f z)+g z • F05RelDD X f z :=
    F05_second_fderivWithin_mul hX (hf.2.2.2.2.1 z.2 hz.2) (hg.2.2.2.2.1 z.2 hz.2) hz.1
  have hT (z : Point n) (hz : z ∈ X ×ˢ I) :
      F05RelT I (fun z => f z*g z) z = F05RelT I f z*g z+f z*F05RelT I g z :=
    derivWithin_fun_mul (hf.2.2.2.2.2 z hz) (hg.2.2.2.2.2 z hz)
  have hTensor : Continuous (fun z : (Space n →L[ℝ] ℝ) × (Space n →L[ℝ] ℝ) =>
      z.1.smulRight z.2) :=
    (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ
      (fun z : (Space n →L[ℝ] ℝ) × (Space n →L[ℝ] ℝ) => z.1.smulRight z.2)).continuous
  refine ⟨hf.1.mul hg.1,?_,?_,?_,?_,?_⟩
  · exact ((hf.1.smul hg.2.1).add (hg.1.smul hf.2.1)).congr hD
  · have hCross1 := hTensor.comp_continuousOn (hf.2.1.prodMk hg.2.1)
    have hCross2 := hTensor.comp_continuousOn (hg.2.1.prodMk hf.2.1)
    exact ((((hf.1.smul hg.2.2.1).add hCross1).add hCross2).add
      (hg.1.smul hf.2.2.1)).congr hH
  · exact ((hf.2.2.2.1.mul hg.1).add (hf.1.mul hg.2.2.2.1)).congr hT
  · intro t ht
    exact (hf.2.2.2.2.1 t ht).mul (hg.2.2.2.2.1 t ht)
  · intro z hz
    exact (hf.2.2.2.2.2 z hz).mul (hg.2.2.2.2.2 z hz)

end Yau.Proofs.F05Aux
