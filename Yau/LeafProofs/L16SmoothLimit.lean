import Yau.LeafProofs.L16MixedSobolev
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace Yau.LeafProofs.L16Aux

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem uniformLimit_exists {X : Type*} {f : ℕ → X → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x,
      |f k x - f l x| < ε) :
    ∃ g : X → ℝ, TendstoUniformly f g atTop := by
  have hc (x : X) : CauchySeq (fun k ↦ f k x) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun k hk l hl ↦ by simpa only [Real.dist_eq] using hN k hk l hl x⟩
  choose g hg using fun x ↦ cauchySeq_tendsto_of_complete (hc x)
  refine ⟨g, tendstoUniformlyOn_univ.mp ?_⟩
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  · apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun k hk l hl x _ ↦ by simpa only [Real.dist_eq] using hN k hk l hl x⟩
  · exact fun x _ ↦ hg x

private theorem tendstoUniformly_finite_pi {I X : Type*} [Fintype I]
    {f : ℕ → X → I → ℝ} {g : X → I → ℝ}
    (h : ∀ i, TendstoUniformly (fun k x ↦ f k x i) (fun x ↦ g x i) atTop) :
    TendstoUniformly f g atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hi : ∀ i, ∀ᶠ k in atTop, ∀ x, dist (g x i) (f k x i) < ε :=
    fun i ↦ Metric.tendstoUniformly_iff.mp (h i) ε hε
  filter_upwards [eventually_all.mpr hi] with k hk
  intro x
  exact (dist_pi_lt_iff hε).mpr (fun i ↦ hk i x)

private theorem piRing_apply_basis {m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] ℝ) (i : Fin m) :
    ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin m) L i =
      L (Pi.single i 1) := rfl

/-- A uniformly Cauchy sequence of all actual coordinate jets has a smooth
limit, and all of its actual coordinate jets converge uniformly. -/
theorem exists_contDiff_uniformLimit_coordinateWordDerivative {m : ℕ}
    {f : ℕ → (Fin m → ℝ) → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hcauchy : ∀ w : List (Fin m), ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x,
        |coordinateWordDerivative (f k) w x - coordinateWordDerivative (f l) w x| < ε) :
    ∃ v : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ v ∧
      ∀ w : List (Fin m), TendstoUniformly
        (fun k ↦ coordinateWordDerivative (f k) w) (coordinateWordDerivative v w) atTop := by
  classical
  choose F hF using fun w ↦ uniformLimit_exists (hcauchy w)
  let e := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin m)
  have he (L : (Fin m → ℝ) →L[ℝ] ℝ) (i : Fin m) :
      e L i = L (Pi.single i 1) := rfl
  have hdlim (w : List (Fin m)) : TendstoUniformly
      (fun k x ↦ fderiv ℝ (coordinateWordDerivative (f k) w) x)
      (fun x ↦ e.symm (fun i ↦ F (i :: w) x)) atTop := by
    have hpi : TendstoUniformly
        (fun k x i ↦ coordinateWordDerivative (f k) (i :: w) x)
        (fun x i ↦ F (i :: w) x) atTop :=
      tendstoUniformly_finite_pi (fun i ↦ hF (i :: w))
    convert e.symm.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformly hpi using 1
    · funext k x
      exact (e.symm_apply_apply (fderiv ℝ (coordinateWordDerivative (f k) w) x)).symm
    · rfl
  have hd (w : List (Fin m)) (x : Fin m → ℝ) :
      HasFDerivAt (F w) (e.symm (fun i ↦ F (i :: w) x)) x :=
    hasFDerivAt_of_tendstoUniformly (hdlim w)
      (fun k x ↦ ((contDiff_coordinateWordDerivative (hf k) w).differentiable (by simp) x).hasFDerivAt)
      (fun x ↦ (hF w).tendsto_at x) x
  have hfd (w : List (Fin m)) :
      fderiv ℝ (F w) = fun x ↦ e.symm (fun i ↦ F (i :: w) x) :=
    funext (fun x ↦ (hd w x).fderiv)
  have hCn : ∀ n : ℕ, ∀ w : List (Fin m), ContDiff ℝ n (F w) := by
    intro n
    induction n with
    | zero =>
        intro w
        exact contDiff_zero.mpr ((hF w).continuous
          (Eventually.of_forall fun k ↦ (contDiff_coordinateWordDerivative (hf k) w).continuous).frequently)
    | succ n ih =>
        intro w
        rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
          contDiff_succ_iff_fderiv]
        refine ⟨fun x ↦ (hd w x).differentiableAt, by simp, ?_⟩
        rw [hfd w]
        exact e.symm.contDiff.comp (contDiff_pi.mpr fun i ↦ ih (i :: w))
  have hword : ∀ w : List (Fin m), coordinateWordDerivative (F []) w = F w := by
    intro w
    induction w with
    | nil => rfl
    | cons i w ih =>
        simp only [coordinateWordDerivative, ih]
        funext x
        rw [hfd w]
        exact (he _ i).symm.trans (congrFun (e.apply_symm_apply (fun i ↦ F (i :: w) x)) i)
  refine ⟨F [], contDiff_infty.mpr (fun n ↦ hCn n []), fun w ↦ ?_⟩
  rw [hword w]
  exact hF w

/-- A pointwise limit agrees almost everywhere with the `L²` limit. The proof
uses Fatou's lemma for the nonnegative squared differences. -/
theorem ae_eq_of_pointwise_tendsto_of_integral_sq_sub_tendsto_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {u v : X → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hv : AEStronglyMeasurable v μ)
    (hpoint : ∀ x, Tendsto (fun k ↦ f k x) atTop (𝓝 (v x)))
    (hL2 : Tendsto (fun k ↦ ∫ x, (f k x - u x) ^ 2 ∂μ) atTop (𝓝 0)) :
    v =ᵐ[μ] u := by
  have hi (k : ℕ) : Integrable (fun x ↦ (f k x - u x) ^ 2) μ :=
    ((hf k).sub hu).integrable_sq
  have hm (k : ℕ) : AEMeasurable (fun x ↦ ENNReal.ofReal ((f k x - u x) ^ 2)) μ :=
    (((hf k).aestronglyMeasurable.sub hu.aestronglyMeasurable).pow 2).aemeasurable.ennreal_ofReal
  have hp (x : X) : Tendsto (fun k ↦ ENNReal.ofReal ((f k x - u x) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal ((v x - u x) ^ 2))) :=
    ENNReal.tendsto_ofReal (((hpoint x).sub tendsto_const_nhds).pow 2)
  have hiLim : Tendsto (fun k ↦ ∫⁻ x, ENNReal.ofReal ((f k x - u x) ^ 2) ∂μ)
      atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hL2
    simp only [ENNReal.ofReal_zero] at h
    convert h using 1
    funext k
    exact (ofReal_integral_eq_lintegral_ofReal (hi k) (ae_of_all μ fun x ↦ sq_nonneg _)).symm
  have hz : (∫⁻ x, ENNReal.ofReal ((v x - u x) ^ 2) ∂μ) = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ = ∫⁻ x, liminf (fun k ↦ ENNReal.ofReal ((f k x - u x) ^ 2)) atTop ∂μ :=
        lintegral_congr fun x ↦ (hp x).liminf_eq.symm
      _ ≤ liminf (fun k ↦ ∫⁻ x, ENNReal.ofReal ((f k x - u x) ^ 2) ∂μ) atTop :=
        lintegral_liminf_le' hm
      _ = 0 := hiLim.liminf_eq
  have hmv : AEMeasurable (fun x ↦ ENNReal.ofReal ((v x - u x) ^ 2)) μ :=
    ((hv.sub hu.aestronglyMeasurable).pow 2).aemeasurable.ennreal_ofReal
  filter_upwards [(lintegral_eq_zero_iff' hmv).mp hz] with x hx
  have hsq : (v x - u x) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
  nlinarith [sq_nonneg (v x - u x)]

/-- The smooth limit reconstructed from actual uniformly Cauchy coordinate jets
represents the original `L²` function whenever the approximants converge to it in `L²`. -/
theorem exists_contDiff_ae_eq_of_coordinateWordDerivative_uniform_cauchy {m : ℕ}
    {f : ℕ → (Fin m → ℝ) → ℝ} {u : (Fin m → ℝ) → ℝ}
    (hf : ∀ k, ContDiff ℝ ∞ (f k)) (hcf : ∀ k, HasCompactSupport (f k))
    (hu : MemLp u 2 volume)
    (hcauchy : ∀ w : List (Fin m), ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x,
        |coordinateWordDerivative (f k) w x - coordinateWordDerivative (f l) w x| < ε)
    (hL2 : Tendsto (fun k ↦ ∫ x, (f k x - u x) ^ 2) atTop (𝓝 0)) :
    ∃ v : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ v ∧ v =ᵐ[volume] u ∧
      ∀ w : List (Fin m), TendstoUniformly
        (fun k ↦ coordinateWordDerivative (f k) w) (coordinateWordDerivative v w) atTop := by
  obtain ⟨v, hv, hvlim⟩ := exists_contDiff_uniformLimit_coordinateWordDerivative hf hcauchy
  refine ⟨v, hv, ?_, hvlim⟩
  apply ae_eq_of_pointwise_tendsto_of_integral_sq_sub_tendsto_zero
      (fun k ↦ ?_) hu hv.continuous.aestronglyMeasurable
      (fun x ↦ (hvlim []).tendsto_at x) hL2
  exact (memLp_two_iff_integrable_sq (hf k).continuous.aestronglyMeasurable).mpr
    (by simpa only [mixedDerivative_empty] using integrable_sq_mixedDerivative (hf k) (hcf k) ∅)

end Yau.LeafProofs.L16Aux
