import Yau.Proofs.V04MatrixSmoothCoordinates
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! A continuous branch of matrix square roots is smooth wherever its
actual Sylvester derivative is invertible. The local inverse is identified
with the same branch by its actual continuity. -/

open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff
open Filter
noncomputable section
namespace Yau.Blueprint.V04Proof

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem contDiffAt_continuous_square_lift (R B : ℝ → Matrix I I ℂ) (t₀ : ℝ)
    (hRc : ContinuousAt R t₀) (hB : ContDiffAt ℝ ∞ B t₀)
    (hsq : ∀ t, R t * R t = B t)
    (L : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ)
    (hL : ∀ X, L X = R t₀ * X + X * R t₀) : ContDiffAt ℝ ∞ R t₀ := by
  let Q : Matrix I I ℂ → Matrix I I ℂ := fun X => X * X
  have hQ : ContDiffAt ℝ ∞ Q (R t₀) := (contDiff_id.mul contDiff_id).contDiffAt
  have hd : HasFDerivAt Q (L : Matrix I I ℂ →L[ℝ] Matrix I I ℂ) (R t₀) := by
    have hraw := (hasFDerivAt_id (𝕜 := ℝ) (R t₀)).mul'
      (hasFDerivAt_id (𝕜 := ℝ) (R t₀))
    apply hraw.congr_fderiv
    apply ContinuousLinearMap.ext
    intro X
    exact (hL X).symm
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let J := hQ.localInverse hd hn
  have hJ : ContDiffAt ℝ ∞ J (B t₀) := by
    have h := hQ.to_localInverse hd hn
    simpa only [Q, hsq t₀] using h
  have hleft : ∀ᶠ X in 𝓝 (R t₀), J (Q X) = X :=
    (hQ.hasStrictFDerivAt' hd hn).eventually_left_inverse
  have heq : R =ᶠ[𝓝 t₀] (fun t => J (B t)) := by
    filter_upwards [hRc.tendsto.eventually hleft] with t ht
    simpa only [Q, hsq t] using ht.symm
  exact (hJ.comp t₀ hB).congr_of_eventuallyEq heq

end Yau.Blueprint.V04Proof
