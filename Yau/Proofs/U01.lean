import Yau.Proofs.U01Limit
import spec.CHAIN.CONTRACTS

/-! The original U01 backward-shadowing theorem, on the same clock and maps.
The stronger finite budget exp(-7s) closes all inverse-tube applications before
any limit is taken. -/
open Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.U01Proof
open Yau Blueprint Blueprint.U03Proof

theorem backward_shadowing (n m : ℕ) : BackwardShadowing n m := by
  intro Ω s G Ginv zeta nu delta hΩ hn hn' hd0 hd hs hstep hauto hhol hraw hlips
  have hinput : ∀ᶠ k in atTop,
      1 ≤ s k ∧ Real.exp (-nu * s k) < 1 / 2 ∧
      (∀ z ∈ Ω, ‖zeta k z‖ ≤ Real.exp (-2 * nu * s k) ∧
        ‖zeta (k + 1) z - (G k).eval (zeta k z)‖ ≤ Real.exp (-10 * s k)) ∧
      (∀ u v : ComplexVector n, ‖u‖ < Real.exp (-nu * s (k + 1)) →
        ‖v‖ < Real.exp (-nu * s (k + 1)) →
        ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤
          Real.exp (s (k + 1) - s k) * ‖u - v‖) := by
    filter_upwards [hs.eventually (eventually_ge_atTop (1 : ℝ)),
      (exp_decay hs hn).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hraw, hlips] with k h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp hinput
  have hlarge : ∀ k, K ≤ k → 1 ≤ s k := fun k hk => (hK k hk).1
  have hsmall : ∀ k, K ≤ k → Real.exp (-nu * s k) < 1 / 2 := fun k hk => (hK k hk).2.1
  have hzeta := fun k hk => (hK k hk).2.2.1
  have hlip := fun k hk => (hK k hk).2.2.2
  have hfin := finite_error hn hn' hd hstep hlarge hsmall hauto hzeta hlip
  have htube := finite_tube hn hn' hd hstep hlarge hsmall hauto hzeta hlip
  have hdiff := terminal_difference hn hn' hd hstep hlarge hsmall hauto hzeta hlip
  classical
  have hex : ∀ k, ∃ f : ComplexVector m → ComplexVector n,
      K ≤ k → TendstoUniformlyOn (fun r => approx Ginv zeta k r) f atTop Ω := by
    intro k
    by_cases hk : K ≤ k
    · obtain ⟨f, hf⟩ := uniform_limit_of_terminal_difference k hs (fun r R z hz => hdiff r R k hk z hz)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 0, fun hk' => (hk hk').elim⟩
  choose xi hxi using hex
  refine ⟨xi, ?_, ?_⟩
  · apply eventually_atTop.mpr
    refine ⟨K, fun k hk => ?_⟩
    have hconv := hxi k hk
    refine ⟨Blueprint.V02FlowProof.differentiableOn_of_uniform_holomorphic_limit
      hΩ Set.Subset.rfl (fun r => approx_differentiableOn Ginv zeta hhol k r) hconv, ?_, ?_⟩
    · intro C hC hcompact
      have h : TendstoUniformlyOn (fun l => approx Ginv zeta k (l - k))
          (xi k) atTop Ω :=
        fun u hu => (tendsto_sub_atTop_nat k).eventually (hconv u hu)
      apply (h.mono hC).congr
      filter_upwards [eventually_ge_atTop k] with l hl z hz
      simp only [approx, Function.comp_def, Nat.add_sub_of_le hl]
    · intro z hz
      have hlimit : ‖xi k z - zeta k z‖ ≤ Real.exp (-7 * s k) :=
        le_of_tendsto ((hconv.tendsto_at hz).sub_const (zeta k z)).norm
          (Eventually.of_forall (fun r => hfin r k hk z hz))
      have h76 : Real.exp (-7 * s k) ≤ Real.exp (-6 * s k) :=
        Real.exp_le_exp.mpr (by linarith [hlarge k hk])
      refine ⟨hlimit.trans h76, ?_⟩
      have hk1 : K ≤ k + 1 := by omega
      have hleft : Tendsto (fun r => approx Ginv zeta k (r + 1) z) atTop (𝓝 (xi k z)) :=
        (hconv.tendsto_at hz).comp (tendsto_add_atTop_nat 1)
      have hright : Tendsto (fun r => (Ginv k).eval (approx Ginv zeta (k + 1) r z))
          atTop (𝓝 ((Ginv k).eval (xi (k + 1) z))) :=
        (polynomial_eval_differentiable (Ginv k)).continuous.continuousAt.tendsto.comp
          ((hxi (k + 1) hk1).tendsto_at hz)
      have heq : xi k z = (Ginv k).eval (xi (k + 1) z) :=
        tendsto_nhds_unique hleft (by simpa only [approx_succ] using hright)
      have hcancel := inverse_eval_forward ⟨(hauto k).2, (hauto k).1⟩ (xi (k + 1) z)
      rw [heq]
      exact hcancel.symm
  · apply eventually_atTop.mpr
    refine ⟨K, fun k hk l hkl i hki hil z hz => ?_⟩
    have hi : K ≤ i := hk.trans hki
    have hil' : i + 1 ≤ l := by omega
    simpa only [approx, Nat.add_sub_of_le hil'] using htube (l - (i + 1)) i hi z hz

end Yau.NodeProofs.U01Proof
namespace Yau.NodeProofs

theorem U01_proved : Blueprint.U01 := U01Proof.backward_shadowing

theorem U01_contract_proved : BlueprintContracts.U01_contract := U01_proved

end Yau.NodeProofs
