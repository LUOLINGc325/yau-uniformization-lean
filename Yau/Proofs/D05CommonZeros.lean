import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.DiscreteSubset

/-! Finite common-zero removal for vector-valued holomorphic sections.
Every quotient is an iterated divided difference of the same section. -/

open Filter Set Function
open scoped Topology

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_dslope {U : Set ℂ} {f : ℂ → E}
    (hf : AnalyticOnNhd ℂ f U) {p : ℂ} (hp : p ∈ U) :
    AnalyticOnNhd ℂ (dslope f p) U := by
  intro z hz
  by_cases hzp : z = p
  · subst z
    obtain ⟨P, hP⟩ := hf p hp
    exact ⟨P.fslope, hP.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℂ (fun z => (z - p)⁻¹ • (f z - f p)) z :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzp)).smul
        ((hf z hz).sub analyticAt_const)
    exact hq.congr (dslope_eventuallyEq_slope_of_ne f hzp).symm

theorem analyticOnNhd_iterate_dslope {U : Set ℂ} {f : ℂ → E}
    (hf : AnalyticOnNhd ℂ f U) {p : ℂ} (hp : p ∈ U) (k : ℕ) :
    AnalyticOnNhd ℂ ((fun g => dslope g p)^[k] f) U := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact analyticOnNhd_dslope ih hp

theorem remove_common_zero_at {U : Set ℂ} {f : ℂ → E}
    (hf : AnalyticOnNhd ℂ f U) {p : ℂ} (hp : p ∈ U)
    (hne : ¬ ∀ᶠ z in 𝓝 p, f z = 0) :
    ∃ (k : ℕ) (g : ℂ → E), AnalyticOnNhd ℂ g U ∧ g p ≠ 0 ∧
      ∀ z, f z = (z - p) ^ k • g z := by
  obtain ⟨P, hP⟩ := hf p hp
  refine ⟨P.order, (fun g => dslope g p)^[P.order] f,
    analyticOnNhd_iterate_dslope hf hp _, ?_, ?_⟩
  · exact hP.iterate_dslope_fslope_ne_zero (fun h => hne (hP.locally_zero_iff.mpr h))
  · exact hP.eq_pow_order_mul_iterate_dslope

theorem remove_common_zeros_in_finset {U : Set ℂ} (hU : IsPreconnected U)
    (s : Finset ℂ) {f : ℂ → E} (hf : AnalyticOnNhd ℂ f U)
    (hs : (s : Set ℂ) ⊆ U) (hne : ∃ z ∈ U, f z ≠ 0) :
    ∃ (ν : ℂ → ℕ) (g : ℂ → E), AnalyticOnNhd ℂ g U ∧
      (∀ p ∈ s, g p ≠ 0) ∧
      ∀ z, f z = (∏ p ∈ s, (z - p) ^ ν p) • g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      exact ⟨fun _ => 0, f, hf, by simp, by simp⟩
  | @insert p s hps ih =>
      obtain ⟨ν, g, hg, hgs, hfg⟩ := ih hf
        (fun z hz => hs (Finset.mem_insert_of_mem hz)) hne
      have hp : p ∈ U := hs (Finset.mem_insert_self _ _)
      have hgn : ¬ ∀ᶠ z in 𝓝 p, g z = 0 := by
        intro hzero
        have hgzero := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hp hzero
        obtain ⟨z, hz, hzne⟩ := hne
        exact hzne (by rw [hfg z, hgzero hz]; simp)
      obtain ⟨k, h, hh, hhp, hgh⟩ := remove_common_zero_at hg hp hgn
      refine ⟨Function.update ν p k, h, hh, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hzs
        · exact hhp
        · intro hzero
          exact hgs z hzs (by rw [hgh z, hzero]; simp)
      · intro z
        have hprod : (∏ a ∈ s, (z - a) ^ Function.update ν p k a) =
            ∏ a ∈ s, (z - a) ^ ν a := by
          apply Finset.prod_congr rfl
          intro a ha
          rw [Function.update_of_ne (ne_of_mem_of_not_mem ha hps)]
        rw [hfg z, hgh z, Finset.prod_insert hps, Function.update_self, hprod,
          mul_smul]
        rw [smul_smul, mul_comm]
        exact mul_smul _ _ _

theorem common_zeros_finite_on_smaller_disc {f : ℂ → E} {R ρ : ℝ}
    (hρR : ρ < R) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hne : ∃ z ∈ Metric.ball (0 : ℂ) R, f z ≠ 0) :
    Set.Finite {z : ℂ | z ∈ Metric.closedBall 0 ρ ∧ f z = 0} := by
  have hnontrivial : ¬ Set.EqOn f 0 (Metric.ball 0 R) := by
    intro hzero
    obtain ⟨z, hz, hzne⟩ := hne
    exact hzne (hzero hz)
  have hcod := (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
    (convex_ball (0 : ℂ) R).isPreconnected).resolve_left hnontrivial
  have hrestrict : {z : ℂ | f z ≠ 0} ∈ codiscreteWithin (Metric.closedBall 0 ρ) :=
    Filter.codiscreteWithin_mono (Metric.closedBall_subset_ball hρR) hcod
  have hfin := (isCompact_closedBall (0 : ℂ) ρ).finite_sdiff_of_mem_codiscreteWithin hrestrict
  convert hfin using 1
  ext z
  simp

theorem remove_common_zeros_on_smaller_disc {f : ℂ → E} {R ρ : ℝ}
    (hρR : ρ < R) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hne : ∃ z ∈ Metric.ball (0 : ℂ) R, f z ≠ 0) :
    ∃ (s : Finset ℂ) (ν : ℂ → ℕ) (g : ℂ → E),
      (∀ p ∈ s, p ∈ Metric.closedBall (0 : ℂ) ρ ∧ f p = 0) ∧
      AnalyticOnNhd ℂ g (Metric.ball 0 R) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) ρ, g z ≠ 0) ∧
      ∀ z, f z = (∏ p ∈ s, (z - p) ^ ν p) • g z := by
  classical
  let hfin := common_zeros_finite_on_smaller_disc hρR hf hne
  let s := hfin.toFinset
  have hs : ∀ p, p ∈ s ↔ p ∈ Metric.closedBall (0 : ℂ) ρ ∧ f p = 0 := by
    intro p
    exact hfin.mem_toFinset
  obtain ⟨ν, g, hg, hgs, hfg⟩ := remove_common_zeros_in_finset
    (convex_ball (0 : ℂ) R).isPreconnected s hf
    (fun p hp => Metric.closedBall_subset_ball hρR (hs p |>.mp hp).1) hne
  refine ⟨s, ν, g, fun p hp => (hs p).mp hp, hg, ?_, hfg⟩
  intro z hz hzero
  have hfz : f z = 0 := by rw [hfg z, hzero]; simp
  exact hgs z ((hs z).mpr ⟨hz, hfz⟩) hzero

end Yau.Blueprint.D05Proof
