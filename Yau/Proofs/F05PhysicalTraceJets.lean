import Yau.Proofs.F05BootstrapNative

/-! Equality on a genuine physical closed set determines the actual
ambient first and second spatial jets there by unique differentiation. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_physical_trace_spatial_jets {X : Set (Space n)} (hX : UniqueDiffOn ℝ X)
    (u v : Point n → ℝ) (τ : ℝ)
    (hu : ∀ x ∈ X, ContDiffAt ℝ 2 (fun y => u (y,τ)) x)
    (hv : ∀ x ∈ X, ContDiffAt ℝ 2 (fun y => v (y,τ)) x)
    (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ)) :
    ∀ x ∈ X, spatialD u (x,τ) = spatialD v (x,τ) ∧
      spatialDD u (x,τ) = spatialDD v (x,τ) := by
  have hFirst (x : Space n) (hx : x ∈ X) :
      F05RelD X u (x,τ) = F05RelD X v (x,τ) :=
    fderivWithin_congr hTrace (hTrace x hx)
  have hNative (x : Space n) (hx : x ∈ X) : spatialD u (x,τ) = spatialD v (x,τ) := by
    rw [← F05RelD_eq_spatialD (hX x hx) ((hu x hx).differentiableAt (by norm_num)),
      ← F05RelD_eq_spatialD (hX x hx) ((hv x hx).differentiableAt (by norm_num))]
    exact hFirst x hx
  intro x hx
  refine ⟨hNative x hx,?_⟩
  rw [← F05RelDD_eq_spatialDD hX hx hu,← F05RelDD_eq_spatialDD hX hx hv]
  exact fderivWithin_congr hFirst (hFirst x hx)

end Yau.Proofs.F05Aux
