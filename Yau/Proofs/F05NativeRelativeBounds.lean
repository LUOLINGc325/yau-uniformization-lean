import Yau.Proofs.F05BootstrapRestrictions
import Yau.Proofs.F05HolderExponentLowering

/-! The proved relative Schauder budgets give the literal native budgets
for an actual ambient C2 representative, without any loss of a derivative. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_native_schauder_of_relative {X : Set (Space n)} {l r α C : ℝ}
    (hX : UniqueDiffOn ℝ X) {u : Point n → ℝ} (hu : C2 (cylinder X l r) u)
    (hRel : F05RelSchauder α X (Icc l r) u C) :
    SchauderBound α (cylinder X l r) u C := by
  have hD (z : Point n) (hz : z ∈ cylinder X l r) : F05RelD X u z = spatialD u z :=
    F05RelD_eq_spatialD (hX z.1 hz.1) ((hu.2.2.2.2.1 z hz).differentiableAt (by norm_num))
  have hDD (z : Point n) (hz : z ∈ cylinder X l r) : F05RelDD X u z = spatialDD u z :=
    F05RelDD_eq_spatialDD hX hz.1 (fun y hy => hu.2.2.2.2.1 (y,z.2) ⟨hy,hz.2⟩)
  refine ⟨hu,hRel.2.1.1,?_,holderBound_congr_on hRel.2.2.1 hDD,
    holderBound_congr_on hRel.2.2.2 (fun z hz => F05RelT_eq_timeD u hz.1)⟩
  intro z hz
  have hPair := hRel.2.1.2.1 z hz
  change max ‖u z‖ ‖F05RelD X u z‖ ≤ C at hPair
  refine ⟨?_,?_⟩
  · simpa only [Real.norm_eq_abs] using (le_max_left ‖u z‖ ‖F05RelD X u z‖).trans hPair
  · rw [← hD z hz]
    exact (le_max_right ‖u z‖ ‖F05RelD X u z‖).trans hPair

theorem F05_relative_schauder_lower_exponent {X : Set (Space n)} {I : Set ℝ} {α β C : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) {u : Point n → ℝ} (hu : F05RelSchauder β X I u C) :
    F05RelSchauder α X I u (2*C) :=
  ⟨hu.1,F05_holder_lower_exponent hα hαβ hu.2.1,
    F05_holder_lower_exponent hα hαβ hu.2.2.1,F05_holder_lower_exponent hα hαβ hu.2.2.2⟩

end Yau.Proofs.F05Aux
