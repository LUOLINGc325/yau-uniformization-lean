import Mathlib
import Yau.Geometry.Basic

/-! A compactly supported function on one target coordinate ball pulls
back through the actual inverse sheet and extends smoothly by zero. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def sheetExtension (O : Set (ComplexVector n)) (θ : ComplexVector n → ComplexVector n)
    (g : ComplexVector n → F) (z : ComplexVector n) : F := by
  classical
  exact if z ∈ O then g (θ z) else 0

theorem sheetExtension_eq_comp_germ (O : Set (ComplexVector n)) (hO : IsOpen O)
    (θ : ComplexVector n → ComplexVector n) (g : ComplexVector n → F)
    (z : ComplexVector n) (hz : z ∈ O) : sheetExtension O θ g =ᶠ[𝓝 z] g ∘ θ := by
  classical
  filter_upwards [hO.mem_nhds hz] with w hw
  exact if_pos hw

theorem sheetExtension_tsupport_subset (O W : Set (ComplexVector n))
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (g : ComplexVector n → F) (hc : HasCompactSupport g) (hs : tsupport g ⊆ W) :
    tsupport (sheetExtension O θ g) ⊆ σ '' tsupport g := by
  classical
  have hK : IsCompact (σ '' tsupport g) := hc.image_of_continuousOn (hσ.mono hs)
  apply closure_minimal _ hK.isClosed
  intro z hz
  change sheetExtension O θ g z ≠ 0 at hz
  by_cases hzo : z ∈ O
  · have hne : g (θ z) ≠ 0 := by simpa only [sheetExtension, if_pos hzo] using hz
    exact ⟨θ z, subset_closure hne, hστ z hzo⟩
  · exact False.elim (hz (by simp only [sheetExtension, if_neg hzo]))

theorem sheetExtension_compactSupport (O W : Set (ComplexVector n))
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (g : ComplexVector n → F) (hc : HasCompactSupport g) (hs : tsupport g ⊆ W) :
    HasCompactSupport (sheetExtension O θ g) :=
  (hc.image_of_continuousOn (hσ.mono hs)).of_isClosed_subset (isClosed_tsupport _)
    (sheetExtension_tsupport_subset O W σ θ hσ hσW hστ g hc hs)

theorem sheetExtension_zero_germ (O W : Set (ComplexVector n))
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (g : ComplexVector n → F) (hc : HasCompactSupport g) (hs : tsupport g ⊆ W)
    (z : ComplexVector n) (hz : z ∉ σ '' tsupport g) :
    sheetExtension O θ g =ᶠ[𝓝 z] fun _ => 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro he
  exact hz (sheetExtension_tsupport_subset O W σ θ hσ hσW hστ g hc hs he)

theorem sheetExtension_contDiff (O W : Set (ComplexVector n)) (hO : IsOpen O)
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (hθ : ContDiffOn ℝ ∞ θ O) (g : ComplexVector n → F) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ W) :
    ContDiff ℝ ∞ (sheetExtension O θ g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hzo : z ∈ O
  · exact ((hg.comp_contDiffOn hθ).contDiffAt (hO.mem_nhds hzo)).congr_of_eventuallyEq
      (sheetExtension_eq_comp_germ O hO θ g z hzo)
  · have hzK : z ∉ σ '' tsupport g := by
      rintro ⟨w, hw, rfl⟩
      exact hzo (hσW (hs hw))
    exact contDiffAt_const.congr_of_eventuallyEq
      (sheetExtension_zero_germ O W σ θ hσ hσW hστ g hc hs z hzK)

theorem sheetExtension_at_section (O W : Set (ComplexVector n))
    (σ θ : ComplexVector n → ComplexVector n) (hσW : MapsTo σ W O)
    (hτσ : ∀ w ∈ W, θ (σ w) = w) (g : ComplexVector n → F)
    (w : ComplexVector n) (hw : w ∈ W) : sheetExtension O θ g (σ w) = g w := by
  classical
  simp only [sheetExtension, if_pos (hσW hw), hτσ w hw]

end Yau.Proofs.C03Aux
