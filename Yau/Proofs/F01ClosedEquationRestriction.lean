import Yau.Proofs.F01SchauderClosedRestriction

/-! The genuine closed-cylinder equation restricts without replacing
its one-sided derivative by an ambient derivative. This supplies every
nested spatial-bootstrap cylinder from the single native equation. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem closed_cylinder_c2_and_timeD_restrict
    {S S' : Set (Space n)} {a b l r : ℝ} {u : Point n → ℝ}
    (hlr : l < r) (hS : S' ⊆ S) (hI : Icc l r ⊆ Icc a b)
    (hu : C2 (cylinder S a b) u) :
    C2 (cylinder S' l r) u ∧ ∀ p ∈ cylinder S' l r,
      timeD (cylinder S' l r) u p = timeD (cylinder S a b) u p := by
  have hSpace : MapsTo (fun x : Space n => (1 : ℝ) • x + 0) S' S := by
    intro x hx
    simpa only [one_smul, add_zero] using hS hx
  have hTime : MapsTo (fun t : ℝ => 0 + (1 : ℝ) ^ 2 * t) (Icc l r) (Icc a b) := by
    intro t ht
    simpa only [one_pow, one_mul, zero_add] using hI ht
  have hPull : affineParabolicPullback 1 (0 : Space n) 0 u = u := by
    funext p
    simp [affineParabolicPullback, affineParabolicPoint]
  have hPoint (p : Point n) : affineParabolicPoint 1 (0 : Space n) 0 p = p := by
    simp [affineParabolicPoint]
  constructor
  · have hh := c2_affineParabolicPullback hlr hu hSpace hTime
    rw [hPull] at hh
    exact hh
  · intro p hp
    have hh := timeD_affineParabolicPullback hlr hu hSpace hTime hp
    rw [hPull, hPoint] at hh
    simpa only [one_pow, one_mul] using hh

theorem closed_cylinder_linear_equation_restrict
    {S S' : Set (Space n)} {a b l r : ℝ} {u f : Point n → ℝ}
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ)
    (hlr : l < r) (hS : S' ⊆ S) (hI : Icc l r ⊆ Icc a b)
    (hu : C2 (cylinder S a b) u)
    (hEq : ∀ p ∈ cylinder S a b, linearOp (cylinder S a b) A B u p = f p) :
    C2 (cylinder S' l r) u ∧
      ∀ p ∈ cylinder S' l r, linearOp (cylinder S' l r) A B u p = f p := by
  obtain ⟨hC2, hTime⟩ := closed_cylinder_c2_and_timeD_restrict hlr hS hI hu
  refine ⟨hC2, ?_⟩
  intro p hp
  unfold linearOp
  rw [hTime p hp]
  exact hEq p ⟨hS hp.1, hI hp.2⟩

end Yau.NodeProofs.F01Aux
