import Yau.Proofs.F05BootstrapRelativeCutoff
import Yau.Proofs.F05BootstrapRelativeMultiplication
import Yau.Proofs.F05BootstrapStationary

/-! Genuine localization of a relative-C2 field across the artificial
edge, followed by a smooth time cutoff on the original physical set. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_spatial_localization {H X V : Set (Space n)} {I : Set ℝ}
    (hH : UniqueDiffOn ℝ H) (hX : UniqueDiffOn ℝ X) (hV : IsOpen V)
    (hVX : H ∩ V ⊆ X) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ V) {u : Point n → ℝ} (hu : F05RelC2 X I u) :
    F05RelC2 H I (fun z => φ z.1*u z) :=
  F05_relative_cutoff_extension hH hX hV hVX hSupport
    (F05_relative_c2_mul hX (F05_relative_spatial_profile hX hφ) hu)

theorem F05_relative_localized_c2 {H X V : Set (Space n)} {I : Set ℝ}
    (hH : UniqueDiffOn ℝ H) (hX : UniqueDiffOn ℝ X) (hI : UniqueDiffOn ℝ I)
    (hV : IsOpen V) (hVX : H ∩ V ⊆ X)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hSupport : tsupport φ ⊆ V)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) {u : Point n → ℝ} (hu : F05RelC2 X I u) :
    F05RelC2 H I (fun z => θ z.2*(φ z.1*u z)) :=
  F05_relative_c2_mul hH (F05_relative_time_profile hI hθ)
    (F05_relative_spatial_localization hH hX hV hVX hφ hSupport hu)

theorem F05_relative_localized_initial {θ : ℝ → ℝ} (hθ : θ 0 = 0)
    (φ : Space n → ℝ) (u : Point n → ℝ) (x : Space n) :
    θ 0*(φ x*u (x,0)) = 0 := by rw [hθ,zero_mul]

theorem F05_relative_localized_face {e : Space n} {I : Set ℝ}
    (θ : ℝ → ℝ) (φ : Space n → ℝ) {u : Point n → ℝ}
    (hu : ∀ x, inner ℝ e x = 0 → ∀ t ∈ I, u (x,t) = 0) :
    ∀ x, inner ℝ e x = 0 → ∀ t ∈ I, θ t*(φ x*u (x,t)) = 0 := by
  intro x hx t ht
  rw [hu x hx t ht,mul_zero,mul_zero]

end Yau.Proofs.F05Aux
