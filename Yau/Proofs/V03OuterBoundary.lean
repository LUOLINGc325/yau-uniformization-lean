import Yau.Proofs.V03OuterCandidate
import Yau.Proofs.V03RealPositiveFourier
import Yau.Proofs.V03OuterUniqueness

/-! The constructed scalar outer function has the exact actual boundary
modulus and positive center. The original realization's supplied h equals it. -/

open scoped Topology ContDiff Matrix
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem positiveDisc_real_boundary {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (θ : ℝ) :
    2 * (positiveDiscProjection (fun t => (q t : ℂ)) (circlePoint θ)).re - circleAverage q = q θ := by
  have hu : ContDiff ℝ ∞ (fun t => (q t : ℂ)) := Complex.ofRealCLM.contDiff.comp hq
  have hup : Function.Periodic (fun t => (q t : ℂ)) (2 * Real.pi) :=
    fun t => congrArg Complex.ofReal (hp t)
  have hqcircle : Continuous hp.lift := hq.continuous.quotient_lift _
  have hlift : (fun x : AddCircle (2 * Real.pi) => (hp.lift x : ℂ)) = hup.lift := by
    funext x
    induction x using Quotient.inductionOn' with
    | h t => rfl
  have hcoeff (k : ℤ) : fourierCoeff (fun x : AddCircle (2 * Real.pi) => (hp.lift x : ℂ)) k =
      circleFourier (fun t => (q t : ℂ)) k := by
    rw [hlift]
    exact (circleFourier_eq_periodic_lift hup k).symm
  have hs : Summable (fourierCoeff (fun x : AddCircle (2 * Real.pi) => (hp.lift x : ℂ))) :=
    (circleFourier_summable hu hup).congr (fun k => (hcoeff k).symm)
  have hr := real_positiveFourier_reconstruction hqcircle hs (θ : AddCircle (2 * Real.pi))
  simp_rw [hcoeff] at hr
  rw [Function.Periodic.lift_coe, circleFourier_ofReal_zero, Complex.ofReal_re] at hr
  rw [positiveDiscProjection_boundary hu hup]
  exact hr

theorem outerExponent_re_boundary {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (a : ℕ) (θ : ℝ) :
    (outerExponent q a (circlePoint θ)).re = (a : ℝ) * q θ := by
  have hh := congrArg (fun t : ℝ => (a : ℝ) * t) (positiveDisc_real_boundary hq hp θ)
  simpa [outerExponent, Complex.mul_re, Complex.sub_re] using hh

theorem outerCandidate_norm_boundary {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (a : ℕ) (θ : ℝ) :
    ‖outerCandidate q a (circlePoint θ)‖ = Real.exp ((a : ℝ) * q θ) := by
  rw [outerCandidate, Complex.norm_exp, outerExponent_re_boundary hq hp]

variable {n r : ℕ} {X : KahlerManifold n}

theorem outerCandidate_logTrace_modulus {d : VariationData X r} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) (θ : ℝ) :
    ‖outerCandidate (logTrace d j F.f) a (circlePoint θ)‖ =
      wallPower d j a (F.f (circlePoint θ)) := by
  rw [outerCandidate_norm_boundary (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F)]
  unfold logTrace wallPower
  rw [Real.exp_nat_mul, Real.exp_log (admissible_wallProduct_bounds hd hF θ).1]

theorem realized_h_eq_outerCandidate (d : VariationData X r) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
      h ζ = outerCandidate (logTrace d j F.f) a ζ := by
  apply holomorphic_eq_of_boundary_modulus_center hR.2.2.2.1
    (outerCandidate_contDiffOn (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F) a)
    (fun ζ _ => outerCandidate_ne_zero _ _ ζ)
  · intro θ
    exact (hR.2.2.2.2.2.2.2.1 θ).trans (outerCandidate_logTrace_modulus hd hF a θ).symm
  · exact (realized_h_center d j a F E l h α fz R hR).trans
      (outerCandidate_logTrace_zero d j a F).symm

end Yau.Blueprint.V03Proof
