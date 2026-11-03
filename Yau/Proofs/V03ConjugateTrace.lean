import Yau.Proofs.V03HarmonicConjugate
import Yau.Proofs.V03OuterBoundary

/-! The real-parameter harmonic conjugate is the boundary trace of the
constructed holomorphic exponent, with the exact original Fourier energy. -/

open scoped Topology ContDiff
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def harmonicConjugateTrace (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (2 * positiveDiscProjection (fun t => (q t : ℂ)) (circlePoint θ) -
    (circleAverage q : ℂ)).im

theorem harmonicConjugateTrace_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) :
    ContDiff ℝ ∞ (harmonicConjugateTrace q) := by
  have hu : ContDiff ℝ ∞ (fun t => (q t : ℂ)) := Complex.ofRealCLM.contDiff.comp hq
  have hup : Function.Periodic (fun t => (q t : ℂ)) (2 * Real.pi) :=
    fun t => congrArg Complex.ofReal (hp t)
  exact Complex.imCLM.contDiff.comp
    ((contDiff_const.mul (closedDisc_trace_contDiff (positiveDiscProjection_contDiffOn hu hup))).sub
      contDiff_const)

theorem harmonicConjugateTrace_periodic (q : ℝ → ℝ) :
    Function.Periodic (harmonicConjugateTrace q) (2 * Real.pi) := by
  intro θ
  unfold harmonicConjugateTrace
  rw [circlePoint_periodic θ]

theorem harmonicConjugateTrace_eq_circle {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (θ : ℝ) :
    harmonicConjugateTrace q θ = harmonicConjugateCircle hp.lift
      (θ : AddCircle (2 * Real.pi)) := by
  have hu : ContDiff ℝ ∞ (fun t => (q t : ℂ)) := Complex.ofRealCLM.contDiff.comp hq
  have hup : Function.Periodic (fun t => (q t : ℂ)) (2 * Real.pi) :=
    fun t => congrArg Complex.ofReal (hp t)
  have hlift : (fun x : AddCircle (2 * Real.pi) => (hp.lift x : ℂ)) = hup.lift := by
    funext x
    induction x using Quotient.inductionOn' with
    | h t => rfl
  have hcoeff (k : ℤ) : fourierCoeff (fun x : AddCircle (2 * Real.pi) => (hp.lift x : ℂ)) k =
      circleFourier (fun t => (q t : ℂ)) k := by
    rw [hlift]
    exact (circleFourier_eq_periodic_lift hup k).symm
  unfold harmonicConjugateTrace harmonicConjugateCircle analyticCircleProjection
  simp only [ContinuousMap.coe_mk, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.const_apply, smul_eq_mul]
  simp_rw [hcoeff]
  rw [positiveDiscProjection_boundary hu hup, circleFourier_ofReal_zero]

theorem scalarDSq_harmonicConjugateTrace {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) :
    scalarDSq (harmonicConjugateTrace q) = scalarDSq q := by
  have hup : Function.Periodic (fun t => (q t : ℂ)) (2 * Real.pi) :=
    fun t => congrArg Complex.ofReal (hp t)
  have hH := harmonicConjugateTrace_periodic q
  have hHp : Function.Periodic (fun t => (harmonicConjugateTrace q t : ℂ)) (2 * Real.pi) :=
    fun t => congrArg Complex.ofReal (hH t)
  have hlift : hup.lift = fun x : AddCircle (2 * Real.pi) => (hp.lift x : ℂ) := by
    funext x
    induction x using Quotient.inductionOn' with
    | h t => rfl
  have hHlift : hHp.lift = fun x : AddCircle (2 * Real.pi) =>
      (harmonicConjugateCircle hp.lift x : ℂ) := by
    funext x
    induction x using Quotient.inductionOn' with
    | h t => exact congrArg Complex.ofReal (harmonicConjugateTrace_eq_circle hq hp t)
  have hu : ContDiff ℝ ∞ (fun t => (q t : ℂ)) := Complex.ofRealCLM.contDiff.comp hq
  have hcoeff : Summable (fourierCoeff (fun x : AddCircle (2 * Real.pi) => (hp.lift x : ℂ))) := by
    have hs := (circleFourier_summable hu hup).congr (fun k => circleFourier_eq_periodic_lift hup k)
    simpa only [hlift] using hs
  unfold scalarDSq
  rw [circleDirichlet_periodic_lift hHp, circleDirichlet_periodic_lift hup]
  change circleDirichlet hHp.lift = circleDirichlet hup.lift
  rw [hHlift, hlift]
  exact harmonicConjugateCircle_dirichlet (hcoeff.comp_injective Nat.cast_injective)

theorem outerExponent_im_boundary (q : ℝ → ℝ) (a : ℕ) (θ : ℝ) :
    (outerExponent q a (circlePoint θ)).im = (a : ℝ) * harmonicConjugateTrace q θ := by
  simp only [outerExponent, harmonicConjugateTrace, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]

theorem outerCandidate_boundary_factorization {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (a : ℕ) (θ : ℝ) :
    outerCandidate q a (circlePoint θ) =
      (Real.exp ((a : ℝ) * q θ) : ℂ) * circlePoint ((a : ℝ) * harmonicConjugateTrace q θ) := by
  unfold outerCandidate circlePoint
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
    exact outerExponent_re_boundary hq hp a θ
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_one, zero_mul, add_zero, zero_add]
    exact outerExponent_im_boundary q a θ

end Yau.Blueprint.V03Proof
