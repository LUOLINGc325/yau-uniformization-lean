import Yau.Proofs.C07HomotopyLift

/-! Compare the original two path lifts with the actual lifted homotopy square. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem homotopy_boundary_lifts_endpoint_eq
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    (H : C(unitInterval × unitInterval, M.Carrier))
    (E : unitInterval × unitInterval → ComplexVector n) (hE : Continuous E)
    (hE₀ : ∀ s, E (0, s) = 0)
    (hEball : ∀ p, E p ∈ Metric.ball 0 r) (hEproj : ∀ p, Φ (E p) = H p)
    (htarget : ∀ s, H (1, s) = H (1, 0))
    (Γ₀ Γ₁ : unitInterval → ComplexVector n) (hΓ₀ : Continuous Γ₀) (hΓ₁ : Continuous Γ₁)
    (hΓ₀ball : ∀ u, Γ₀ u ∈ Metric.ball 0 r) (hΓ₁ball : ∀ u, Γ₁ u ∈ Metric.ball 0 r)
    (hΓ₀proj : ∀ u, Φ (Γ₀ u) = H (u, 0)) (hΓ₁proj : ∀ u, Φ (Γ₁ u) = H (u, 1))
    (hΓ₀zero : Γ₀ 0 = 0) (hΓ₁zero : Γ₁ 0 = 0) : Γ₀ 1 = Γ₁ 1 := by
  have hrows (s : unitInterval) : Continuous (fun u : unitInterval => E (u, s)) := by
    have hmap : Continuous (fun u : unitInterval => (u, s)) :=
      continuous_id.prodMk continuous_const
    exact hE.comp hmap
  have hcomp₀ : Φ ∘ Γ₀ = Φ ∘ (fun u : unitInterval => E (u, 0)) := by
    funext u
    exact (hΓ₀proj u).trans (hEproj (u, 0)).symm
  have hcomp₁ : Φ ∘ Γ₁ = Φ ∘ (fun u : unitInterval => E (u, 1)) := by
    funext u
    exact (hΓ₁proj u).trans (hEproj (u, 1)).symm
  have heq₀ := chart_lifts_unique hΦ hΓ₀ (hrows 0) hΓ₀ball
    (fun u => hEball (u, 0)) hcomp₀ (0 : unitInterval) (hΓ₀zero.trans (hE₀ 0).symm)
  have heq₁ := chart_lifts_unique hΦ hΓ₁ (hrows 1) hΓ₁ball
    (fun u => hEball (u, 1)) hcomp₁ (0 : unitInterval) (hΓ₁zero.trans (hE₀ 1).symm)
  have hend := chart_lift_homotopy_endpoint hΦ H E hEball hEproj hE₀ hrows htarget (1 : unitInterval)
  exact (congrFun heq₀ 1).trans (hend.symm.trans (congrFun heq₁ 1).symm)

end Yau.Proofs.C07Aux
