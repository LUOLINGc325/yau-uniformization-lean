import Yau.Proofs.V03ConjugateTrace
import Yau.Proofs.V03WallPowerDirichlet

/-! Universal boundary phase and full outer-trace half-order bounds. The
constants depend on the exponent, not on a positive lower wall margin. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem outer_phase_boundaryDSq_le {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (a : ℕ) :
    boundaryDSq (fun θ (_ : Unit) => circlePoint ((a : ℝ) * harmonicConjugateTrace q θ)) ≤
      ENNReal.ofReal ((a : ℝ) ^ 2) * scalarDSq q := by
  have hh := boundaryDSq_exp_phase_le (harmonicConjugateTrace_contDiff hq hp).continuous
    (harmonicConjugateTrace_periodic q) (a : ℝ)
  rwa [scalarDSq_harmonicConjugateTrace hq hp] at hh

theorem outerCandidate_boundaryDSq_le {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (hq0 : ∀ θ, q θ ≤ 0) (a : ℕ) :
    boundaryDSq (fun θ (_ : Unit) => outerCandidate q a (circlePoint θ)) ≤
      ENNReal.ofReal (4 * (a : ℝ) ^ 2) * scalarDSq q := by
  have hprod : (fun θ (_ : Unit) => outerCandidate q a (circlePoint θ)) =
      fun θ (_ : Unit) => (Real.exp ((a : ℝ) * q θ) : ℂ) *
        circlePoint ((a : ℝ) * harmonicConjugateTrace q θ) := by
    funext θ _
    exact outerCandidate_boundary_factorization hq hp a θ
  rw [hprod]
  have hu : Continuous (fun θ => (Real.exp ((a : ℝ) * q θ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hq.continuous))
  have hv : Continuous (fun θ => circlePoint ((a : ℝ) * harmonicConjugateTrace q θ)) :=
    circlePoint_contDiff.continuous.comp
      (continuous_const.mul (harmonicConjugateTrace_contDiff hq hp).continuous)
  have hup : Function.Periodic (fun θ => (Real.exp ((a : ℝ) * q θ) : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg (fun t => (Real.exp ((a : ℝ) * t) : ℂ)) (hp θ)
  have hvp : Function.Periodic (fun θ => circlePoint ((a : ℝ) * harmonicConjugateTrace q θ))
      (2 * Real.pi) := fun θ => congrArg (fun t => circlePoint ((a : ℝ) * t))
        (harmonicConjugateTrace_periodic q θ)
  have hb := boundaryDSq_mul_le hu hv hup hvp (M := 1) (N := 1) (by norm_num) (by norm_num)
    (fun θ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg a) (hq0 θ)))
    (fun θ => (circlePoint_norm _).le)
  have he := scalarDSq_exp_nonpos_le hq.continuous hp hq0 (Nat.cast_nonneg a)
  have hph := outer_phase_boundaryDSq_le hq hp a
  simp only [one_pow, mul_one, scalarDSq] at hb he
  calc
    _ ≤ ENNReal.ofReal 2 *
        (ENNReal.ofReal ((a : ℝ) ^ 2) * scalarDSq q) +
        ENNReal.ofReal 2 * (ENNReal.ofReal ((a : ℝ) ^ 2) * scalarDSq q) := by
      exact hb.trans (add_le_add (mul_le_mul_right he _) (mul_le_mul_right hph _))
    _ = ENNReal.ofReal (4 * (a : ℝ) ^ 2) * scalarDSq q := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring

variable {n r : ℕ} {X : KahlerManifold n}

theorem realized_h_boundary_factorization (d : VariationData X r) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (θ : ℝ) :
    h (circlePoint θ) = (wallPower d j a (F.f (circlePoint θ)) : ℂ) *
      circlePoint ((a : ℝ) * harmonicConjugateTrace (logTrace d j F.f) θ) := by
  rw [realized_h_eq_outerCandidate d hd j a F hF E l h α fz R hR _ (circlePoint_mem_closedBall θ),
    outerCandidate_boundary_factorization (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F),
    ← congrFun (wallPower_trace_eq_exp hd hF a) θ]

theorem realized_h_normalized_phase (d : VariationData X r) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (θ : ℝ) :
    h (circlePoint θ) / (wallPower d j a (F.f (circlePoint θ)) : ℂ) =
      circlePoint ((a : ℝ) * harmonicConjugateTrace (logTrace d j F.f) θ) := by
  rw [realized_h_boundary_factorization d hd j a F hF E l h α fz R hR θ]
  have hn : (wallPower d j a (F.f (circlePoint θ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (admissible_wallPower_bounds hd hF a θ).1)
  exact mul_div_cancel_left₀ _ hn

theorem realized_h_phase_boundaryDSq_le (d : VariationData X r) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    boundaryDSq (fun θ (_ : Unit) =>
      h (circlePoint θ) / (wallPower d j a (F.f (circlePoint θ)) : ℂ)) ≤
      ENNReal.ofReal ((a : ℝ) ^ 2) * scalarDSq (logTrace d j F.f) := by
  simp_rw [realized_h_normalized_phase d hd j a F hF E l h α fz R hR]
  exact outer_phase_boundaryDSq_le (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F) a

theorem realized_h_boundaryDSq_le (d : VariationData X r) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    boundaryDSq (fun θ (_ : Unit) => h (circlePoint θ)) ≤
      ENNReal.ofReal (4 * (a : ℝ) ^ 2) * scalarDSq (logTrace d j F.f) := by
  have heq : (fun θ (_ : Unit) => h (circlePoint θ)) =
      fun θ (_ : Unit) => outerCandidate (logTrace d j F.f) a (circlePoint θ) := by
    funext θ _
    exact realized_h_eq_outerCandidate d hd j a F hF E l h α fz R hR _ (circlePoint_mem_closedBall θ)
  rw [heq]
  exact outerCandidate_boundaryDSq_le (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F)
    (admissible_logTrace_nonpos hd hF) a

end Yau.Blueprint.V03Proof
