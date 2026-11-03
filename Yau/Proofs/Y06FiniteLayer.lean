import Yau.Proofs.Y06ProjectionDynamics
import Yau.Proofs.Y06FiniteBackward

/-! The homogeneous correction is an actual finite backward recursion,
with identity resets represented by zero nonlinear layers. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

def finiteLayerCorrection (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n) : ℕ → PolyMap n :=
  backwardValue b (fun k X => if active k then backwardAffineStep (D k) (J k) (w k) (B k) X else 0) 0

theorem finiteLayerCorrection_terminal (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n)
    {k : ℕ} (hk : b ≤ k) : finiteLayerCorrection b active D J w B k = 0 :=
  backwardValue_terminal b _ 0 hk

theorem finiteLayerCorrection_step (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n)
    {k : ℕ} (hk : k < b) (hactive : active k) :
    finiteLayerCorrection b active D J w B k = backwardAffineStep (D k) (J k) (w k) (B k)
      (finiteLayerCorrection b active D J w B (k + 1)) := by
  rw [finiteLayerCorrection, backwardValue_step b _ 0 hk, ite_eq_left hactive]

theorem finiteLayerCorrection_inactive (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n)
    {k : ℕ} (hactive : ¬active k) : finiteLayerCorrection b active D J w B k = 0 := by
  by_cases hk : k < b
  · rw [finiteLayerCorrection, backwardValue_step b _ 0 hk, ite_eq_right hactive]
  · exact finiteLayerCorrection_terminal b active D J w B (by omega)

theorem finiteLayerCorrection_homogeneous (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n)
    (hB : ∀ k, Homogeneous (B k) m) :
    ∀ k, Homogeneous (finiteLayerCorrection b active D J w B k) m := by
  have hbelow : ∀ k, k ≤ b → Homogeneous (finiteLayerCorrection b active D J w B k) m := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      rw [finiteLayerCorrection_terminal b active D J w B le_rfl]
      exact homogeneous_zero m
    | of_succ k hk ih =>
      by_cases hact : active k
      · rw [finiteLayerCorrection_step b active D J w B hk hact]
        exact backwardAffineStep_homogeneous (D k) (J k) (w k) (hB k) ih
      · rw [finiteLayerCorrection_inactive b active D J w B hact]
        exact homogeneous_zero m
  intro k
  by_cases hk : k ≤ b
  · exact hbelow k hk
  · rw [finiteLayerCorrection_terminal b active D J w B (by omega)]
    exact homogeneous_zero m

def finiteLayerForcing (b : ℕ) (active : ℕ → Prop) (D J : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n) (k : ℕ) : PolyMap n :=
  (linearPolynomial (J k)⁻¹).comp
    ((finiteLayerCorrection b active D J w B (k + 1)).comp (linearPolynomial (J k * D k))) + B k

def finiteLayerModel (b : ℕ) (active : ℕ → Prop) (D J : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n) (k : ℕ) : PolyMap n :=
  if active k then allowedProjection (w k) (finiteLayerForcing b active D J w B k) else 0

theorem finiteLayerModel_homogeneous (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n)
    (hB : ∀ k, Homogeneous (B k) m) (k : ℕ) :
    Homogeneous (finiteLayerModel b active D J w B k) m := by
  by_cases hk : active k
  · rw [finiteLayerModel, ite_eq_left hk]
    apply allowedProjection_homogeneous
    apply homogeneous_add _ (hB k)
    apply homogeneous_linear_comp
    exact homogeneous_comp_linear (finiteLayerCorrection_homogeneous b active D J w B hB (k + 1)) _
  · rw [finiteLayerModel, ite_eq_right hk]
    exact homogeneous_zero m

theorem finiteLayer_equation (b : ℕ) (active : ℕ → Prop)
    (a : ℕ → Fin n → ℂ) (ha : ∀ k i, a k i ≠ 0) (J : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n) {k : ℕ} (hk : k < b) (hactive : active k) :
    let D := fun k => Matrix.diagonal (a k)
    (linearPolynomial (D k)).comp (finiteLayerCorrection b active D J w B k) +
      finiteLayerModel b active D J w B k = finiteLayerForcing b active D J w B k := by
  dsimp only
  rw [finiteLayerModel, ite_eq_left hactive, finiteLayerCorrection_step b active _ J w B hk hactive]
  exact backwardAffineStep_layer_equation (a k) (ha k) (J k) (w k) (B k)
    (finiteLayerCorrection b active (fun k => Matrix.diagonal (a k)) J w B (k + 1))

end Yau.Proofs.Y06Aux
