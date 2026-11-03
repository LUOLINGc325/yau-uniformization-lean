import Yau.Proofs.F01BootstrapRestriction
import Yau.Proofs.F01ClosedPotentialWordEquations

/-! The spatial bootstrap retains the actual terminal time face.
Every order contains the same backward half cylinder, and restrictions
use the within derivative on that face. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

def backwardBootstrapCylinder (n k : ℕ) : Set (Point n) :=
  cylinder (ball 0 (bootstrapRadius k)) (-bootstrapRadius k) 0

theorem backwardBootstrapCylinder_subset_initial (k : ℕ) :
    backwardBootstrapCylinder n k ⊆ cylinder (ball 0 1) (-1) 0 := by
  have hr := (bootstrapRadius_bounds k).2
  intro p hp
  exact ⟨ball_subset_ball hr hp.1, by linarith [hp.2.1], hp.2.2⟩

theorem backward_bootstrap_schauder_restrict {j k : ℕ} {β C : ℝ} {u : Point n → ℝ}
    (hjk : j ≤ k) (hu : SchauderBound β (backwardBootstrapCylinder n j) u C) :
    SchauderBound β (backwardBootstrapCylinder n k) u C := by
  have hr := bootstrapRadius_antitone hjk
  have hbounds := bootstrapRadius_bounds k
  exact schauderBound_closed_cylinder_restrict (by linarith : -bootstrapRadius k < (0 : ℝ))
    (ball_subset_ball hr) (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hu

theorem initial_schauder_backward_bootstrap_restrict (k : ℕ) {β C : ℝ} {u : Point n → ℝ}
    (hu : SchauderBound β (cylinder (ball 0 1) (-1) 0) u C) :
    SchauderBound β (backwardBootstrapCylinder n k) u C := by
  have hr := bootstrapRadius_bounds k
  exact schauderBound_closed_cylinder_restrict (by linarith : -bootstrapRadius k < (0 : ℝ))
    (ball_subset_ball hr.2) (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hu

theorem potentialWordEquations_backward_bootstrap_restrict
    {S : Point n → Matrix (Fin n) (Fin n) ℂ} {u : Point n → ℝ} {d : Space n → ℝ} {v : Space n}
    (hEq : PotentialWordEquationsOn (cylinder (ball 0 1) (-1) 0) S u d v) (k : ℕ) :
    PotentialWordEquationsOn (backwardBootstrapCylinder n k) S u d v := by
  intro vs
  have hh := hEq vs
  have hr := bootstrapRadius_bounds k
  exact closed_cylinder_linear_equation_restrict _ _
    (by linarith : -bootstrapRadius k < (0 : ℝ)) (ball_subset_ball hr.2)
    (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hh.1 hh.2

theorem backward_bootstrap_core_subset (k : ℕ) :
    cylinder (ball (0 : Space n) (1 / 2)) (-(1 / 2)) 0 ⊆ backwardBootstrapCylinder n k := by
  have hr := (bootstrapRadius_bounds k).1.le
  intro p hp
  exact ⟨ball_subset_ball hr hp.1, by linarith [hp.2.1], hp.2.2⟩

end Yau.NodeProofs.F01Aux
