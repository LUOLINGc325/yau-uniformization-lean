import Yau.Proofs.D05CommonZeros
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Local holomorphic projections and removal of common zeros inside the
same varying ambient subbundle. These are proof-local geometric predicates. -/

open Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LocallyProjectedOn (B : ℂ → Submodule ℂ E) (U : Set ℂ) : Prop :=
  ∀ p ∈ U, ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
    ∃ P : ℂ → E →L[ℂ] E, ContDiffOn ℂ ∞ P V ∧
      (∀ z ∈ V, ∀ v, P z v ∈ B z) ∧
      ∀ z ∈ V, ∀ v ∈ B z, P z v = v

theorem eventually_nhdsNE_notMem_finite {S : Set ℂ} (hS : S.Finite) (p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, z ∉ S := by
  have hp : p ∈ (S \ {p})ᶜ := by simp
  have havoid : (S \ {p})ᶜ ∈ 𝓝[≠] p := nhdsWithin_le_nhds
    ((hS.sdiff).isClosed.isOpen_compl.mem_nhds hp)
  filter_upwards [havoid, self_mem_nhdsWithin] with z hz hzp
  intro hzS
  exact hz ⟨hzS, hzp⟩

theorem mem_bundle_of_eventually_mem {B : ℂ → Submodule ℂ E} {U : Set ℂ}
    (hB : LocallyProjectedOn B U) {p : ℂ} (hp : p ∈ U) {g : ℂ → E}
    (hg : ContinuousAt g p) (hmem : ∀ᶠ z in 𝓝[≠] p, g z ∈ B z) :
    g p ∈ B p := by
  obtain ⟨V, hV, hpV, hVU, P, hP, hPrange, hPfix⟩ := hB p hp
  have hPc := ((hP p hpV).contDiffAt (hV.mem_nhds hpV)).continuousAt
  have hleft : ContinuousAt (fun z => P z (g z)) p := hPc.clm_apply hg
  have heq : (fun z => P z (g z)) =ᶠ[𝓝[≠] p] g := by
    filter_upwards [hmem, nhdsWithin_le_nhds (hV.mem_nhds hpV)] with z hz hzV
    exact hPfix z hzV (g z) hz
  have hpe : P p (g p) = g p := tendsto_nhds_unique_of_eventuallyEq
    hleft.continuousWithinAt hg.continuousWithinAt heq
  rw [← hpe]
  exact hPrange p hpV (g p)

theorem remove_common_zeros_in_bundle {B : ℂ → Submodule ℂ E} {f : ℂ → E}
    {ρ R : ℝ} (hρR : ρ < R)
    (hB : LocallyProjectedOn B (Metric.ball 0 R))
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hfm : ∀ z ∈ Metric.ball (0 : ℂ) R, f z ∈ B z)
    (hfn : ∃ z ∈ Metric.ball (0 : ℂ) R, f z ≠ 0) :
    ∃ g : ℂ → E, AnalyticOnNhd ℂ g (Metric.ball 0 R) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) ρ, g z ≠ 0) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, g z ∈ B z := by
  classical
  obtain ⟨s, ν, g, hs, hg, hgne, hfg⟩ := remove_common_zeros_on_smaller_disc hρR hf hfn
  have hgm (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) (hzs : z ∉ s) : g z ∈ B z := by
    have hc : (∏ p ∈ s, (z - p) ^ ν p) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      exact pow_ne_zero _ (sub_ne_zero.mpr (fun hzp => hzs (hzp ▸ hp)))
    have heq : g z = (∏ p ∈ s, (z - p) ^ ν p)⁻¹ • f z := by
      rw [hfg z, inv_smul_smul₀ hc]
    rw [heq]
    exact (B z).smul_mem _ (hfm z hz)
  refine ⟨g, hg, hgne, ?_⟩
  intro p hp
  have hpR : p ∈ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hρR.le hp
  apply mem_bundle_of_eventually_mem hB hpR (hg p hpR).continuousAt
  filter_upwards [eventually_nhdsNE_notMem_finite s.finite_toSet p,
    nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hpR)] with z hzs hzR
  exact hgm z hzR hzs

end Yau.Blueprint.D05Proof
