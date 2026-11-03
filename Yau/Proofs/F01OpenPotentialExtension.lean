import Yau.Proofs.F01OpenOperators

/-! A restricted potential is extended by zero only as a value function.
Its restriction, time equation and actual native Levi tensor are retained
exactly on the genuine open manifold; no boundary smoothness is asserted. -/
noncomputable section
open Set TopologicalSpace
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

def openExtendedPotential
    (U : (openConnectedManifold M S hS).Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) : ℝ := by
  classical
  exact if hx : x ∈ S then U ⟨x, hx⟩ t else 0

theorem openExtendedPotential_restrict
    (U : (openConnectedManifold M S hS).Carrier → ℝ → ℝ)
    (x : (openConnectedManifold M S hS).Carrier) (t : ℝ) :
    openExtendedPotential M S hS U x.val t = U x t := by
  simp only [openExtendedPotential, x.property, dite_true]
  rfl

theorem openExtendedPotential_levi
    (U : (openConnectedManifold M S hS).Carrier → ℝ → ℝ)
    (x : (openConnectedManifold M S hS).Carrier) (t : ℝ) :
    levi (fun y => openExtendedPotential M S hS U y t) x.val = levi (fun y => U y t) x := by
  have heq : (fun y : (openConnectedManifold M S hS).Carrier =>
      openExtendedPotential M S hS U y.val t) = fun y => U y t :=
    funext (fun y => openExtendedPotential_restrict M S hS U y t)
  rw [← openRestriction_levi M S hS (fun y => openExtendedPotential M S hS U y t) x, heq]

theorem openExtendedPotential_time_equation
    (U : (openConnectedManifold M S hS).Carrier → ℝ → ℝ)
    (P : (openConnectedManifold M S hS).Carrier → ℝ → ℝ) {I : Set ℝ}
    (hU : ∀ x t, t ∈ I → HasDerivWithinAt (U x) (P x t) I t)
    (x : (openConnectedManifold M S hS).Carrier) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (openExtendedPotential M S hS U x.val) (P x t) I t := by
  have heq : openExtendedPotential M S hS U x.val = U x :=
    funext (fun s => openExtendedPotential_restrict M S hS U x s)
  rw [heq]
  exact hU x t ht

end Yau.NodeProofs.F01Aux
