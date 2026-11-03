import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-! Finite harmonic polynomials approximate arbitrary continuous real boundary data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open scoped ComplexConjugate Topology
open Set Polynomial
namespace Yau.NodeProofs.P07Aux.SupportWeak

private theorem fourier_nat (m : ℕ) (θ : AddCircle (1 : ℝ)) :
    fourier (m : ℤ) θ = (AddCircle.toCircle θ : ℂ) ^ m := by
  induction m with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ m ih =>
    rw [Nat.cast_succ, fourier_add, ih, fourier_one, pow_succ]

/-- The full complex span is represented before taking real parts. -/
theorem fourierSpan_polynomial_conj_polynomial
    {t : C(AddCircle (1 : ℝ), ℂ)}
    (ht : t ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) :
    ∃ P Q : Polynomial ℂ, ∀ θ : AddCircle (1 : ℝ),
      t θ = P.eval (AddCircle.toCircle θ : ℂ) +
        conj (Q.eval (AddCircle.toCircle θ : ℂ)) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨m, rfl⟩ := ht
    cases m with
    | ofNat m =>
      refine ⟨X ^ m, 0, fun θ => ?_⟩
      simp only [eval_pow, eval_X, eval_zero, map_zero, add_zero]
      exact fourier_nat m θ
    | negSucc m =>
      refine ⟨0, X ^ (m + 1), fun θ => ?_⟩
      simp only [eval_zero, eval_pow, eval_X, zero_add]
      rw [show Int.negSucc m = -((m + 1 : ℕ) : ℤ) from rfl, fourier_neg,
        fourier_nat]
  | zero => exact ⟨0, 0, by simp⟩
  | add t s ht hs htrep hsrep =>
    obtain ⟨P, Q, hPQ⟩ := htrep
    obtain ⟨R, S, hRS⟩ := hsrep
    refine ⟨P + R, Q + S, fun θ => ?_⟩
    simp only [ContinuousMap.add_apply, eval_add, map_add, hPQ, hRS]
    ring
  | smul a t ht hrep =>
    obtain ⟨P, Q, hPQ⟩ := hrep
    refine ⟨C a * P, C (conj a) * Q, fun θ => ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul, hPQ, eval_mul, eval_C,
      map_mul, starRingEnd_self_apply]
    ring

/-- Uniform approximation on the actual boundary sphere by a finite polynomial. -/
theorem exists_re_polynomial_boundary_approx
    {k : ℂ → ℝ} (hk : ContinuousOn k (Metric.closedBall (0 : ℂ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, ‖z‖ = 1 → |(p.eval z).re - k z| < ε := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let b : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun θ => (k (AddCircle.toCircle θ : ℂ) : ℂ), by
      apply Complex.continuous_ofReal.comp
      apply hk.comp_continuous (show Continuous (fun θ : AddCircle (1 : ℝ) => (AddCircle.toCircle θ : ℂ)) by fun_prop)
      intro θ
      exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right, Circle.norm_coe] using (le_refl (1 : ℝ)))⟩
  have hb : b ∈ closure (↑(Submodule.span ℂ
      (Set.range (fourier (T := (1 : ℝ))))) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨t, ht, hdist⟩ := Metric.mem_closure_iff.mp hb ε hε
  obtain ⟨P, Q, hPQ⟩ := fourierSpan_polynomial_conj_polynomial ht
  refine ⟨P + Q, fun z hz => ?_⟩
  let zc : Circle := ⟨z, by change z ∈ Metric.sphere 0 1; simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
  obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective zc
  have hzθ : (AddCircle.toCircle θ : ℂ) = z := by
    exact congrArg (fun q : Circle => (q : ℂ))
      ((AddCircle.homeomorphCircle_apply one_ne_zero θ).symm.trans hθ)
  have htε : ‖t θ - b θ‖ < ε :=
    (ContinuousMap.norm_coe_le_norm (t - b) θ).trans_lt (by
      simpa only [dist_eq_norm, norm_sub_rev] using hdist)
  have hre : (t θ - b θ).re = ((P + Q).eval z).re - k z := by
    rw [hPQ, hzθ]
    simp [b, hzθ, map_add]
  rw [← hre]
  exact (Complex.abs_re_le_norm _).trans_lt htε

/-- The approximant is an actual harmonic function, with its actual center mean. -/
theorem harmonicOnNhd_re_polynomial (p : Polynomial ℂ) :
    InnerProductSpace.HarmonicOnNhd (fun z => (p.eval z).re) Set.univ := by
  intro z hz
  exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) p) z hz).harmonicAt_re

end Yau.NodeProofs.P07Aux.SupportWeak
