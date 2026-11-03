import Yau.Proofs.F05BootstrapDefinitions
import Yau.LeafProofs.L16InteriorPatchJets

/-! Actual within jets agree on a cutoff plateau, even at the physical
plane and the terminal time. No extension of the equation is used. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_cutoff_plateau_jets {X : Set (Space n)} {I : Set ℝ}
    {φ : Space n → ℝ} {θ : ℝ → ℝ} (u : Point n → ℝ) {z : Point n}
    (hφ : φ =ᶠ[𝓝 z.1] (fun _ => 1)) (hθ : θ =ᶠ[𝓝 z.2] (fun _ => 1)) :
    F05RelD X (fun p => θ p.2*(φ p.1*u p)) z = F05RelD X u z ∧
      F05RelDD X (fun p => θ p.2*(φ p.1*u p)) z = F05RelDD X u z ∧
      F05RelT I (fun p => θ p.2*(φ p.1*u p)) z = F05RelT I u z := by
  have hEq : (fun x => θ z.2*(φ x*u (x,z.2))) =ᶠ[𝓝 z.1] (fun x => u (x,z.2)) := by
    filter_upwards [hφ] with x hx
    rw [hθ.self_of_nhds,hx,one_mul,one_mul]
  have hD : fderivWithin ℝ (fun x => θ z.2*(φ x*u (x,z.2))) X =ᶠ[𝓝 z.1]
      fderivWithin ℝ (fun x => u (x,z.2)) X := by
    filter_upwards [eventually_eventually_nhds.2 hEq] with x hx
    have hxEq : (fun y => θ z.2*(φ y*u (y,z.2))) =ᶠ[𝓝 x] (fun y => u (y,z.2)) := hx
    exact hxEq.fderivWithin_eq_of_nhds
  refine ⟨hEq.fderivWithin_eq_of_nhds,hD.fderivWithin_eq_of_nhds,?_⟩
  have hTime : (fun t => θ t*(φ z.1*u (z.1,t))) =ᶠ[𝓝 z.2] (fun t => u (z.1,t)) := by
    filter_upwards [hθ] with t ht
    rw [ht,hφ.self_of_nhds,one_mul,one_mul]
  exact hTime.derivWithin_eq_of_nhds

theorem F05_relative_interiorPatch_jets_at_top {X : Set (Space n)} {I : Set ℝ}
    {δ h σ : ℝ} (hδ : 0 < δ) (hh : 0 < h) (c : Space n) (u : Point n → ℝ) :
    F05RelD X (classicalInteriorPatch δ h σ hh c u) (c,localSchauderTime δ h) =
        F05RelD X u (c,localSchauderTime δ h+σ) ∧
      F05RelDD X (classicalInteriorPatch δ h σ hh c u) (c,localSchauderTime δ h) =
        F05RelDD X u (c,localSchauderTime δ h+σ) ∧
      F05RelT I (classicalInteriorPatch δ h σ hh c u) (c,localSchauderTime δ h) =
        F05RelT I (timeTranslate σ u) (c,localSchauderTime δ h) := by
  have hT : 0 < localSchauderTime δ h := by unfold localSchauderTime; positivity
  exact F05_relative_cutoff_plateau_jets (timeTranslate σ u)
    (innerPatchBump_eventually_one (by positivity) c) (initialTimeCutoff_eventually_one hT)

end Yau.Proofs.F05Aux
