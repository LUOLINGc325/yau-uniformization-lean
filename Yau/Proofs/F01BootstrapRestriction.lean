import Yau.Proofs.F01BootstrapCylinders
import Yau.Proofs.F01ClosedEquationRestriction
import Yau.Proofs.F01NormalizedWordEquations

/-! All induction cylinders lie in the one native initial cylinder.
Earlier estimates and the same actual scalar word equation restrict to
them, with their genuine closed-face time derivatives. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem bootstrapRadius_antitone : Antitone bootstrapRadius := by
  apply antitone_nat_of_succ_le
  intro k
  have hb := bootstrap_buffer_data k
  linarith [hb.1]

theorem bootstrapCylinder_antitone : Antitone (bootstrapCylinder n) := by
  intro j k hjk p hp
  have hr := bootstrapRadius_antitone hjk
  exact ⟨ball_subset_ball hr hp.1, by linarith [hp.2.1], hp.2.2⟩

theorem bootstrapCylinder_subset_initial (k : ℕ) :
    bootstrapCylinder n k ⊆ cylinder (ball 0 1) (-1) 1 := by
  have hr := (bootstrapRadius_bounds k).2
  intro p hp
  exact ⟨ball_subset_ball hr hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩

theorem bootstrap_schauder_restrict {j k : ℕ} {β C : ℝ} {u : Point n → ℝ}
    (hjk : j ≤ k) (hu : SchauderBound β (bootstrapCylinder n j) u C) :
    SchauderBound β (bootstrapCylinder n k) u C := by
  have hr := bootstrapRadius_antitone hjk
  have hbounds := bootstrapRadius_bounds k
  apply schauderBound_closed_cylinder_restrict (by linarith : -bootstrapRadius k < (1 / 2 : ℝ))
    (ball_subset_ball hr) (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hu

theorem initial_schauder_bootstrap_restrict (k : ℕ) {β C : ℝ} {u : Point n → ℝ}
    (hu : SchauderBound β (cylinder (ball 0 1) (-1) 1) u C) :
    SchauderBound β (bootstrapCylinder n k) u C := by
  have hr := bootstrapRadius_bounds k
  apply schauderBound_closed_cylinder_restrict (by linarith : -bootstrapRadius k < (1 / 2 : ℝ))
    (ball_subset_ball hr.2) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) hu

theorem potentialWordEquations_bootstrap_restrict
    {S : Point n → Matrix (Fin n) (Fin n) ℂ} {u : Point n → ℝ} {d : Space n → ℝ}
    {v : Space n} (hEq : PotentialSpatialWordEquations S u d v) (k : ℕ) :
    let H := chartPotentialMatrix S u
    let w := spatialDerivativeWord [v] u
    let f := fun p => traceWith (H p)
      (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ d p.1 v
    ∀ vs : List (Space n), C2 (bootstrapCylinder n k) (spatialDerivativeWord vs w) ∧
      ∀ p ∈ bootstrapCylinder n k,
        linearOp (bootstrapCylinder n k) (fun q => scalarSymbol (H q)) (fun _ _ => 0)
          (spatialDerivativeWord vs w) p =
          linearCommutatorSource (fun q => scalarSymbol (H q)) w f vs p := by
  dsimp only
  intro vs
  have hh := hEq vs
  have hr := bootstrapRadius_bounds k
  exact closed_cylinder_linear_equation_restrict _ _
    (by linarith : -bootstrapRadius k < (1 / 2 : ℝ)) (ball_subset_ball hr.2)
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) hh.1 hh.2

end Yau.NodeProofs.F01Aux
