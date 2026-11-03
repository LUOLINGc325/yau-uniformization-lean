import Yau.Proofs.V04SmoothSqrtCalculus
import Yau.Proofs.V04SquareInverseSmooth

/-! The actual regularized spectral square root is smooth. At each point,
the fixed-basis Sylvester inverse gives a smooth inverse to matrix squaring;
continuity identifies that inverse with the same spectral branch. -/

open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof

namespace V04SmoothSqrt

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem regularMatrixRoot_contDiff {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ → Matrix I I ℂ) (hA : ContDiff ℝ ∞ A)
    (hH : ∀ t, (A t).IsHermitian) :
    ContDiff ℝ ∞ (fun t => regularMatrixRoot δ (A t)) := by
  let R : ℝ → Matrix I I ℂ := fun t => regularMatrixRoot δ (A t)
  let B : ℝ → Matrix I I ℂ := fun t =>
    A t * A t + algebraMap ℝ (Matrix I I ℂ) (δ ^ 2)
  have hB : ContDiff ℝ ∞ B := (hA.mul hA).add contDiff_const
  have hRc : Continuous R := regularMatrixRoot_continuous δ hA.continuous hH
  have hsq : ∀ t, R t * R t = B t := fun t =>
    regularMatrixRoot_square δ (A t) (hH t)
  apply contDiff_iff_contDiffAt.mpr
  intro t₀
  have hinj : Function.Injective (matrixSylvester (R t₀)) :=
    regularMatrixRoot_sylvester_injective hδ (A t₀) (hH t₀)
  let L : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ :=
    (LinearEquiv.ofInjectiveEndo (matrixSylvester (R t₀)) hinj).toContinuousLinearEquiv
  have hL : ∀ X, L X = R t₀ * X + X * R t₀ := fun _ => rfl
  exact contDiffAt_continuous_square_lift R B t₀ hRc.continuousAt
    hB.contDiffAt hsq L hL

end V04SmoothSqrt

open Yau Yau.Blueprint V04SmoothSqrt

theorem smoothMajorant_entry_contDiff
    {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ → CotangentMatrix n)
    (hA : ∀ i k, ContDiff ℝ ∞ (fun θ => A θ i k))
    (hH : ∀ θ, (A θ).IsHermitian)
    (i k : CotangentIndex n) :
    ContDiff ℝ ∞ (fun θ => smoothMajorant δ (A θ) i k) := by
  have hAm : ContDiff ℝ ∞ A := matrix_contDiff_of_entries A hA
  have hR := regularMatrixRoot_contDiff hδ A hAm hH
  have hM : ContDiff ℝ ∞ (fun t => smoothMajorant δ (A t)) := by
    have heq : (fun t => smoothMajorant δ (A t)) =
        (fun t => algebraMap ℝ (CotangentMatrix n) δ +
          (1 / 2 : ℝ) • (A t + regularMatrixRoot δ (A t))) :=
      funext fun t => smoothMajorant_eq_regularMatrixRoot δ (A t) (hH t)
    rw [heq]
    exact contDiff_const.add ((hAm.add hR).const_smul (1 / 2 : ℝ))
  exact matrix_entry_contDiff hM i k

end Yau.Blueprint.V04Proof
