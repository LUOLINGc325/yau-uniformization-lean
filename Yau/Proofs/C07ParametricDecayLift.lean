import Yau.Proofs.C07ParametricShortLift
import Yau.Proofs.C07FlowSmooth

/-! Original compact metric decay gives uniformly small lifts of a fixed bounded curve family. -/

open scoped Manifold Topology
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem sqrt_exp_neg_mul (a s : ℝ) :
    Real.sqrt (Real.exp (-a * s)) = Real.exp (-(a / 2) * s) := by
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem eventually_joint_lift_of_compact_decay {A : Type*} [TopologicalSpace A]
    (hflow : FlowStage X o h U P ρ) (hwindow : RicciWindows X o h ρ)
    {r c C t₀ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (Φ : ℝ → ComplexVector n → Pt X)
    (hcharts : ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r c C)
    {x : A → Pt X} (γ : ∀ a, IntegrableCurve X.metric.form o (x a))
    (H : C(unitInterval × A, Pt X)) (hH : ∀ p, H p = (γ p.2).1 p.1)
    {K : Set (Pt X)} (hK : IsCompact K)
    (htrace : ∀ a, ∀ u ∈ Icc (0 : ℝ) 1, (γ a).1 u ∈ K)
    (L : ℝ) (hlength : ∀ a, curveLength X.metric.form (γ a).1 ≤ L) :
    ∃ a B T : ℝ, 0 < a ∧ 0 ≤ B ∧ t₀ ≤ T ∧
      ∀ t, T ≤ t → ∃ E : unitInterval × A → ComplexVector n,
        Continuous E ∧ (∀ z, E (0, z) = 0) ∧
        (∀ p, E p ∈ Metric.ball 0 r ∧ Φ t (E p) = H p) ∧
        ∀ p, ‖E p‖ ≤ B * Real.exp (-a * ρ o t) := by
  have hs : Tendsto (ρ o) atTop atTop := hwindow.2.2.1
  obtain ⟨a, ha, T₁, hmetric⟩ := hwindow.2.2.2.2.2.2.1 K hK
  let L₀ := max 1 L
  have hL₀ : 0 < L₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdecay : Tendsto (fun t => Real.exp (-(a / 2) * ρ o t) * L₀) atTop (𝓝 0) := by
    have hz := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (show 0 < a / 2 by positivity) hs)).mul_const L₀
    simpa only [Function.comp_def, zero_mul, neg_mul] using hz
  have htarget : 0 < Real.sqrt (2 * c) * r :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hr
  obtain ⟨T₂, hsmall⟩ := eventually_atTop.mp (hdecay.eventually (Iio_mem_nhds htarget))
  let T := max 0 (max t₀ (max T₁ T₂))
  have hT₀ : 0 ≤ T := le_max_left _ _
  have hTchart : t₀ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT₁ : T₁ ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hT₂ : T₂ ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨a / 2, (Real.sqrt (2 * c))⁻¹ * L₀, T, by positivity,
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hL₀.le, hTchart, ?_⟩
  intro t ht
  have hshort : Real.sqrt (Real.exp (-a * ρ o t)) * L₀ < Real.sqrt (2 * c) * r := by
    rw [sqrt_exp_neg_mul]
    exact hsmall t (hT₂.trans ht)
  obtain ⟨E, hE, hE₀, hEp, hEnorm⟩ := exists_joint_short_lift
    (flow_metricSmooth hflow (hT₀.trans ht)) hr hc (hcharts t (hTchart.trans ht))
    γ H hH (Real.exp_pos _).le
    (fun z u hu => (hmetric t (hT₁.trans ht) _ (htrace z u hu)).2)
    (fun z => (hlength z).trans (le_max_right _ _)) hshort
  refine ⟨E, hE, hE₀, hEp, ?_⟩
  intro p
  have hn := hEnorm p
  rw [sqrt_exp_neg_mul] at hn
  convert hn using 1 <;> ring

end Yau.Proofs.C07Aux
