import Yau.Proofs.F05BootstrapLocalizedC2
import Yau.Proofs.F05BootstrapRelativeCommutator
import Yau.Proofs.F05BootstrapTimeCommutator

/-! The exact localized equation is valid on the original physical set.
All artificial-edge terms are computed commutators, with no reflected PDE
and no prescribed value on the artificial sphere. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_spatial_cutoff_extension_operator {H X V : Set (Space n)} {I : Set ℝ}
    (hH : UniqueDiffOn ℝ H) (hX : UniqueDiffOn ℝ X) (hV : IsOpen V)
    (hVX : H ∩ V ⊆ X) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ V) {u f : Point n → ℝ} (hu : F05RelC2 X I u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (hPDE : ∀ z ∈ X ×ˢ I, F05RelOp X I a b u z = f z)
    {z : Point n} (hz : z ∈ H ×ˢ I) :
    F05RelOp H I a b (fun p => φ p.1*u p) z =
      φ z.1*f z-F05RelSpatialCommutator X a b φ u z := by
  by_cases hzSupport : z.1 ∈ tsupport φ
  · have hzLocal : z ∈ (H ∩ V) ×ˢ I := ⟨⟨hz.1,hSupport hzSupport⟩,hz.2⟩
    have hzX : z ∈ X ×ˢ I := ⟨hVX hzLocal.1,hz.2⟩
    have hProduct := F05_relative_c2_mul hX (F05_relative_spatial_profile hX hφ) hu
    obtain ⟨hD,hDD⟩ := F05_relative_local_domain_jets hH hX hV hVX hProduct hzLocal
    calc
      F05RelOp H I a b (fun p => φ p.1*u p) z =
          F05RelOp X I a b (fun p => φ p.1*u p) z := by unfold F05RelOp; rw [hD,hDD]
      _ = φ z.1*f z-F05RelSpatialCommutator X a b φ u z := by
        rw [F05_relative_spatial_cutoff_operator hX hφ hu a b hzX,hPDE z hzX]
  · obtain ⟨hValue,hD,hDD,hTime⟩ := F05_relative_cutoff_zero_jets H I φ u hzSupport
    have hφ0 : φ z.1 = 0 := image_eq_zero_of_notMem_tsupport hzSupport
    have hDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ) hzSupport
    have hDDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (show z.1 ∉ tsupport (fderiv ℝ φ) from fun h => hzSupport (tsupport_fderiv_subset ℝ h))
    simp only [F05RelOp,hD,hDD,hTime,hφ0,F05RelSpatialCommutator,hDφ,hDDφ,
      zero_apply,zero_mul,mul_zero,Finset.sum_const_zero,add_zero,sub_zero]

theorem F05_localized_relative_cutoff_equation {H X V : Set (Space n)} {I : Set ℝ}
    (hH : UniqueDiffOn ℝ H) (hX : UniqueDiffOn ℝ X) (hI : UniqueDiffOn ℝ I)
    (hV : IsOpen V) (hVX : H ∩ V ⊆ X)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hSupport : tsupport φ ⊆ V)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) {u f : Point n → ℝ} (hu : F05RelC2 X I u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (hPDE : ∀ z ∈ X ×ˢ I, F05RelOp X I a b u z = f z) :
    F05RelC2 H I (fun z => θ z.2*(φ z.1*u z)) ∧
      ∀ z ∈ H ×ˢ I, F05RelOp H I a b (fun p => θ p.2*(φ p.1*u p)) z =
        θ z.2*(φ z.1*f z-F05RelSpatialCommutator X a b φ u z)+deriv θ z.2*(φ z.1*u z) := by
  have hSpatial := F05_relative_spatial_localization hH hX hV hVX hφ hSupport hu
  refine ⟨F05_relative_localized_c2 hH hX hI hV hVX hφ hSupport hθ hu,?_⟩
  intro z hz
  rw [F05_relative_time_cutoff_operator hH hI hθ hSpatial a b hz,
    F05_relative_spatial_cutoff_extension_operator hH hX hV hVX hφ hSupport hu a b hPDE hz]

theorem F05_localized_relative_source_initial_zero (X : Set (Space n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (φ : Space n → ℝ)
    (u f : Point n → ℝ) {θ : ℝ → ℝ} (hθZero : θ =ᶠ[𝓝 0] (fun _ => 0)) (x : Space n) :
    θ 0*(φ x*f (x,0)-F05RelSpatialCommutator X a b φ u (x,0))+
      deriv θ 0*(φ x*u (x,0)) = 0 := by
  have hθ0 : θ 0 = 0 := hθZero.self_of_nhds
  have hθD : deriv θ 0 = 0 := by simpa only [deriv_const] using hθZero.deriv_eq
  rw [hθ0,hθD,zero_mul,zero_mul,zero_add]

end Yau.Proofs.F05Aux
