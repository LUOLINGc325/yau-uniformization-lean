import Yau.Proofs.U02ChartPath
import Yau.Proofs.U02RawSeparation
import Yau.Proofs.U02RawCharts

/-! The original metric comparison turns raw separation into injectivity
of the same corrected limit, using only the indicated immersed sheet. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint
open Yau.LeafProofs.L12Aux

theorem corrected_limit_injective {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho) (hw : RicciWindows X o h rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {psi : Pt X → ComplexVector n}
    (hshadow : ∀ K : Set (Pt X), IsCompact K → ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖(forwardComp G k).eval (psi x) - (H k).eval (f (tk k) x)‖ ≤
        Real.exp (-6 * rho o (tk k))) : Function.Injective psi := by
  intro x y heq
  by_contra hxy
  have hdistpos : 0 < inducedDistance X.metric.form x y := by
    have hn := X.metric.induced_distance_nonneg x y
    have hne : inducedDistance X.metric.form x y ≠ 0 :=
      fun hh => hxy (X.metric.induced_distance_eq_zero.mp hh)
    exact lt_of_le_of_ne hn (Ne.symm hne)
  let R := inducedDistance X.metric.form x y / 2
  have hR : 0 < R := by dsimp [R]; positivity
  let K : Set (Pt X) := {x, y}
  have hK : IsCompact K := isCompact_singleton.insert x
  have hxK : x ∈ K := by simp [K]
  have hyK : y ∈ K := by simp [K]
  have hraw := raw_compact_data hf hc hp ht hK
  have hu : ∀ᶠ k in atTop, ‖f (tk k) x‖ ≤ Real.exp (-sigma * rho o (tk k)) := by
    filter_upwards [hraw] with k hk
    exact hk.choose_spec.2.2.2.2 x hxK
  have hv : ∀ᶠ k in atTop, ‖f (tk k) y‖ ≤ Real.exp (-sigma * rho o (tk k)) := by
    filter_upwards [hraw] with k hk
    exact hk.choose_spec.2.2.2.2 y hyK
  have hsep := models_raw_separation hp hc.2.2.1 hu hv
    ((hshadow K hK).mono fun _ hk => hk x hxK)
    ((hshadow K hK).mono fun _ hk => hk y hyK) heq
  have hball := isCompact_inducedDistance_sublevel X.metric x R
  obtain ⟨cK, _hcK, T, hmetric⟩ := hw.2.2.2.2.2.2.1 _ hball
  let D := Real.sqrt (2 * C)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hdecay : Tendsto (fun k => D * Real.exp (-4 * rho o (tk k))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hp.2.1.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (tendsto_const_nhds.mul hh : Tendsto (fun k => D * _) atTop (𝓝 (D * 0)))
  have hbad : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [hraw, hsep, eventually_models_time_ge hf hp ht (max t0 T),
      hdecay.eventually (gt_mem_nhds hR)] with k hk hsepk htime hshort
    obtain ⟨V, _hV, hKV, _hdf, hinv, _hsmall⟩ := hk
    have hcx := hc.2.2.2.2.1 (tk k) ((le_max_left _ _).trans htime)
    have hell : 0 < Real.exp (-rho o (tk k)) := Real.exp_pos _
    have hellsq : Real.exp (-rho o (tk k)) ^ 2 = Real.exp (-2 * rho o (tk k)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hlower : ∀ z, inducedDistance X.metric.form x z ≤ R →
        HermLE (((Real.exp (-rho o (tk k)) ^ 2 : ℝ) : ℂ) • gMat X.metric.form z)
          (gMat (h (tk k)) z) := by
      intro z hz
      rw [hellsq]
      exact (hmetric (tk k) ((le_max_right _ _).trans htime) z hz).1
    have hbudget : D / Real.exp (-rho o (tk k)) * ‖f (tk k) y - f (tk k) x‖ < R := by
      calc
        _ ≤ D / Real.exp (-rho o (tk k)) * Real.exp (-5 * rho o (tk k)) :=
          mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hsepk)
            (div_nonneg hD hell.le)
        _ = D * Real.exp (-4 * rho o (tk k)) := by
          rw [Real.exp_neg, div_eq_mul_inv, inv_inv, mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ < R := hshort
    have hd := unitaryChart_short_segment X.metric (h (tk k)) o x (Phi (tk k))
      hcx hc.2.2.2.1 hell hR hlower
      (hinv x (hKV hxK)).1 (hinv y (hKV hyK)).1 (hinv x (hKV hxK)).2.1 hbudget
    rw [(hinv y (hKV hyK)).2.1] at hd
    dsimp [R] at hd
    linarith
  obtain ⟨k, hk⟩ := hbad.exists
  exact hk

end Yau.NodeProofs.U02Proof
