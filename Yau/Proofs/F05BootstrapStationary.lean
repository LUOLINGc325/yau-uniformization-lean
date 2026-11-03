import Yau.Proofs.F05BootstrapNative

/-! Smooth spatial and temporal cutoffs give genuine relative C2 fields.
Only ordinary one-variable derivatives of the temporal cutoff are used. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_spatial_profile {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) :
    F05RelC2 X I (fun z => φ z.1) := by
  have hD (z : Point n) (hz : z ∈ X ×ˢ I) :
      F05RelD X (fun z => φ z.1) z = fderiv ℝ φ z.1 :=
    F05RelD_eq_spatialD (hX z.1 hz.1) (hφ.differentiable (by norm_num) z.1)
  have hDD (z : Point n) (hz : z ∈ X ×ˢ I) :
      F05RelDD X (fun z => φ z.1) z = fderiv ℝ (fderiv ℝ φ) z.1 :=
    F05RelDD_eq_spatialDD hX hz.1 (fun x hx => hφ.contDiffAt)
  have hT (z : Point n) : F05RelT I (fun z => φ z.1) z = 0 := by
    simp only [F05RelT,derivWithin_fun_const,Pi.zero_apply]
  have hDC : Continuous (fun z : Point n => fderiv ℝ φ z.1) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous.comp continuous_fst
  have hHC : Continuous (fun z : Point n => fderiv ℝ (fderiv ℝ φ) z.1) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuous.comp continuous_fst
  refine ⟨(hφ.continuous.comp continuous_fst).continuousOn,
    hDC.continuousOn.congr hD,hHC.continuousOn.congr hDD,
    (continuousOn_const (c := (0 : ℝ))).congr (fun z hz => hT z),?_,?_⟩
  · intro t ht
    exact hφ.contDiffOn
  · intro z hz
    exact differentiableWithinAt_const (φ z.1)

theorem F05_relative_time_profile {X : Set (Space n)} {I : Set ℝ}
    (hI : UniqueDiffOn ℝ I) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) :
    F05RelC2 X I (fun z => θ z.2) := by
  have hD (z : Point n) : F05RelD X (fun z => θ z.2) z = 0 := by
    simp only [F05RelD,fderivWithin_fun_const,Pi.zero_apply]
  have hDD (z : Point n) : F05RelDD X (fun z => θ z.2) z = 0 := by
    simp only [F05RelDD,F05RelD,fderivWithin_fun_const,Pi.zero_apply]
  have hT (z : Point n) (hz : z ∈ X ×ˢ I) : F05RelT I (fun z => θ z.2) z = deriv θ z.2 :=
    (hθ.differentiable (by norm_num) z.2).hasDerivAt.hasDerivWithinAt.derivWithin (hI z.2 hz.2)
  refine ⟨(hθ.continuous.comp continuous_snd).continuousOn,
    (continuousOn_const (c := (0 : Space n →L[ℝ] ℝ))).congr (fun z hz => hD z),
    (continuousOn_const (c := (0 : Space n →L[ℝ] Space n →L[ℝ] ℝ))).congr (fun z hz => hDD z),
    (hθ.continuous_deriv_one.comp continuous_snd).continuousOn.congr hT,?_,?_⟩
  · intro t ht
    change ContDiffOn ℝ 2 (fun _ : Space n => θ t) X
    exact contDiffOn_const
  · intro z hz
    exact (hθ.differentiable (by norm_num) z.2).differentiableWithinAt

end Yau.Proofs.F05Aux
