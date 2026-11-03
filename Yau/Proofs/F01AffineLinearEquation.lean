import Yau.Proofs.F01ClosedBackwardRestriction
import Yau.Proofs.F01LinearSpatialCommutator

/-! The actual closed-face linear equation transforms under the same
affine parabolic coordinates as the C2 and Holder estimates. The open
lower face of the original backward-cylinder estimate is then restricted
from that closed equation. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem linearOp_affineParabolicPullback_zero_drift
    {S O : Set (Space n)} {l r a b ρ τ : ℝ} {c : Space n}
    (A : Point n → Mat n) {u : Point n → ℝ}
    (hab : a < b) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    {p : Point n} (hp : p ∈ cylinder O a b) :
    linearOp (cylinder O a b) (fun q => A (affineParabolicPoint ρ c τ q))
      (fun _ _ => 0) (affineParabolicPullback ρ c τ u) p =
      ρ ^ 2 * linearOp (cylinder S l r) A (fun _ _ => 0) u
        (affineParabolicPoint ρ c τ p) := by
  rw [linearOp_zero_drift_eq_contraction, linearOp_zero_drift_eq_contraction,
    timeD_affineParabolicPullback hab hu hSpace hClock hp,
    spatialDD_affineParabolicPullback]
  simp only [map_smul, smul_eq_mul]
  ring

theorem affineParabolicPullback_backward_equation
    {S : Set (Space n)} {l r ρ τ R : ℝ} {c : Space n}
    (A : Point n → Mat n) (f : Point n → ℝ) {u : Point n → ℝ}
    (hR : 0 < R) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) (Metric.ball 0 R) S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc (-(R ^ 2)) 0) (Icc l r))
    (hEq : ∀ p ∈ cylinder S l r, linearOp (cylinder S l r) A (fun _ _ => 0) u p = f p) :
    ∀ p ∈ backward R, linearOp (backward R)
      (fun q => A (affineParabolicPoint ρ c τ q)) (fun _ _ => 0)
      (affineParabolicPullback ρ c τ u) p =
      ρ ^ 2 * f (affineParabolicPoint ρ c τ p) := by
  intro p hp
  have hc : p ∈ cylinder (Metric.ball 0 R) (-(R ^ 2)) 0 :=
    ⟨hp.1, hp.2.1.le, hp.2.2⟩
  dsimp only [backward] at hp ⊢
  rw [← linearOp_closed_open_lower
    (fun q => A (affineParabolicPoint ρ c τ q)) (fun _ _ => 0)
    (affineParabolicPullback ρ c τ u) hp]
  rw [linearOp_affineParabolicPullback_zero_drift A (by nlinarith [sq_pos_of_pos hR])
    hu hSpace hClock hc]
  rw [hEq _ ⟨hSpace hc.1, hClock hc.2⟩]

theorem elliptic_comp_mapsTo {Q Q' : Set (Point n)} {A : Point n → Mat n}
    {ell upper : ℝ} {φ : Point n → Point n}
    (hA : Elliptic Q A ell upper) (hφ : MapsTo φ Q' Q) :
    Elliptic Q' (fun p => A (φ p)) ell upper :=
  ⟨hA.1, hA.2.1, fun p hp => hA.2.2 (φ p) (hφ hp)⟩

end Yau.NodeProofs.F01Aux
