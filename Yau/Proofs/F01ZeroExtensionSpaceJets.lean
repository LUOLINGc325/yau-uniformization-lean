import Yau.Proofs.F01ClampedTimeContinuity
import Yau.Geometry.ParabolicCalculus

/-! The actual zero extension commutes with spatial differentiation.
Zero initial values on an open spatial domain force both initial spatial
jets to vanish there, by locality of the actual Fréchet derivatives. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem spatialD_forwardZeroSpaceTime (F : Point n → ℝ) :
    spatialD (forwardZeroSpaceTime F) = forwardZeroSpaceTime (spatialD F) := by
  funext p
  by_cases ht : p.2 ≤ 0 <;> simp [spatialD, forwardZeroSpaceTime, forwardZeroExtension, ht]

theorem spatialDD_forwardZeroSpaceTime (F : Point n → ℝ) :
    spatialDD (forwardZeroSpaceTime F) = forwardZeroSpaceTime (spatialDD F) := by
  funext p
  by_cases ht : p.2 ≤ 0 <;> simp [spatialDD, forwardZeroSpaceTime, forwardZeroExtension, ht]

theorem spatialD_initial_zero {F : Point n → ℝ} {S : Set (Space n)} (hS : IsOpen S)
    (hF0 : ∀ x ∈ S, F (x, 0) = 0) {x : Space n} (hx : x ∈ S) :
    spatialD F (x, 0) = 0 := by
  have heq : (fun z => F (z, 0)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hS.mem_nhds hx] with z hz
    exact hF0 z hz
  change fderiv ℝ (fun z => F (z, 0)) x = 0
  rw [heq.fderiv_eq]
  simp

theorem spatialDD_initial_zero {F : Point n → ℝ} {S : Set (Space n)} (hS : IsOpen S)
    (hF0 : ∀ x ∈ S, F (x, 0) = 0) {x : Space n} (hx : x ∈ S) :
    spatialDD F (x, 0) = 0 := by
  have heq : (fun z => fderiv ℝ (fun w => F (w, 0)) z) =ᶠ[𝓝 x]
      (fun _ => (0 : Space n →L[ℝ] ℝ)) := by
    filter_upwards [hS.mem_nhds hx] with z hz
    exact spatialD_initial_zero hS hF0 hz
  change fderiv ℝ (fun z => fderiv ℝ (fun w => F (w, 0)) z) x = 0
  rw [heq.fderiv_eq]
  simp

end Yau.NodeProofs.F01Aux
