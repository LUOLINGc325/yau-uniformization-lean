import Yau.Proofs.C03EnvelopeSmoothingKernel
import Yau.Proofs.C03EnvelopeSmoothingUniform

/-! A genuine corrected-circle inequality supplies the exact lower Levi bound. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Filter Set
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.Blueprint Yau.LeafProofs L22Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem complexLeviQuadratic_lower_of_corrected_circles
    (g : ComplexVector n → ℝ) (hg : ContDiff ℝ ∞ g)
    (z v : ComplexVector n) (A : ℝ)
    (hcircle : ∀ᶠ r : ℝ in 𝓝 0,
      g z + A * r ^ 2 ≤
        circleAverage (fun θ => g (z + r • (Complex.exp (θ * Complex.I) • v)))) :
    A ≤ complexLeviQuadratic g z v := by
  let M : ℝ → ℝ := angularLineMean g z v
  let h : ℝ → ℝ := fun r => M r - A * r ^ 2
  have hmin : IsLocalMin h 0 := by
    change ∀ᶠ r in 𝓝 0, h 0 ≤ h r
    filter_upwards [hcircle] with r hr
    change M 0 - A * (0 : ℝ) ^ 2 ≤ M r - A * r ^ 2
    have h0 : M 0 = g z := angularLineMean_zero g z v
    have hMr : M r = circleAverage (fun theta => g (z + r • (Complex.exp (theta * Complex.I) • v))) := rfl
    rw [h0, hMr]
    nlinarith
  have hMc : ContinuousAt M 0 := (hasDerivAt_angularLineMean hg z v 0).continuousAt
  have hc : ContinuousAt h 0 := hMc.sub (continuousAt_const.mul (continuousAt_id.pow 2))
  have hprime : deriv M =
      fun r => circleAverage (fun θ => fderiv ℝ g
        (z + r • (Complex.exp (θ * Complex.I) • v))
        (Complex.exp (θ * Complex.I) • v)) :=
    funext (fun r => (hasDerivAt_angularLineMean hg z v r).deriv)
  have hDM : HasDerivAt (deriv M)
      ((fderiv ℝ (fderiv ℝ g) z v v +
        fderiv ℝ (fderiv ℝ g) z (Complex.I • v) (Complex.I • v)) / 2) 0 := by
    rw [hprime]
    simpa only [zero_smul, add_zero, circleAverage_bilinear] using
      hasDerivAt_angularLineMean_derivative hg z v 0
  have hderiv : deriv h = fun r => deriv M r - A * (2 * r) := by
    funext r
    have hp : HasDerivAt (fun s : ℝ => A * s ^ 2) (A * (2 * r)) r := by
      simpa using (hasDerivAt_pow 2 r).const_mul A
    rw [hprime]
    exact ((hasDerivAt_angularLineMean hg z v r).sub hp).deriv
  have hpD : HasDerivAt (fun r : ℝ => A * (2 * r)) (2 * A) 0 := by
    have heq : (fun r : ℝ => A * (2 * r)) = (fun r : ℝ => (2 * A) * id r) := by
      funext r
      simp only [id_eq]
      ring
    rw [heq]
    simpa only [mul_one] using (hasDerivAt_id 0).const_mul (2 * A)
  have hDD := (hDM.sub hpD).deriv
  change deriv (fun r => deriv M r - A * (2 * r)) 0 = _ at hDD
  have hnonneg := second_deriv_nonneg_of_localMin hmin hc
  rw [hderiv, hDD] at hnonneg
  dsimp only [complexLeviQuadratic]
  linarith

theorem hermLE_levi_of_quadratic_lower
    (g : ComplexVector n → ℝ) (hg : ContDiff ℝ ∞ g)
    (z : ComplexVector n) (H : Herm n) (hH : H.IsHermitian) (A : ℝ)
    (hlower : ∀ v, A * matrixQuadratic H v ≤ complexLeviQuadratic g z v) :
    HermLE ((A : ℂ) • H) (leviC g z) := by
  have hg2 : ContDiffAt ℝ 2 g z := hg.contDiffAt.of_le (by simp)
  have hAH : (((A : ℂ) • H) : Herm n).IsHermitian := by
    change ((A : ℂ) • H)ᴴ = (A : ℂ) • H
    rw [Matrix.conjTranspose_smul, hH.eq]
    simp
  have hHerm : (leviC g z - (A : ℂ) • H).IsHermitian :=
    (leviC_isHermitian hg2).sub hAH
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · have hl := hlower (WithLp.toLp 2 v)
    have hr : matrixQuadratic (leviC g z) (WithLp.toLp 2 v) =
        complexLeviQuadratic g z (WithLp.toLp 2 v) :=
      leviC_quadratic_re hg2 _
    change 0 ≤ matrixQuadratic (leviC g z - (A : ℂ) • H) (WithLp.toLp 2 v)
    rw [matrixQuadratic_sub, matrixQuadratic_real_matrix_smul, hr]
    linarith
  · simpa only [RCLike.im_to_complex] using
      (hHerm.im_star_dotProduct_mulVec_self v).symm

end Yau.Proofs.C03Aux.EnvelopeSmoothing

