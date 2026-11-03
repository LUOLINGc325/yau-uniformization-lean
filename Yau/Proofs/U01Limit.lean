import Yau.Proofs.U01Finite
import Yau.Proofs.V02FlowUniformLimit

/-! Uniform convergence of the actual finite inverse iterates, without evaluating
an inverse outside the tubes proved in U01Finite. -/
open Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.U01Proof
open Yau
variable {n m : ℕ} {Ω : Set (ComplexVector m)}
    {s : ℕ → ℝ} {Ginv : ℕ → PolyMap n}
    {zeta : ℕ → ComplexVector m → ComplexVector n}

theorem uniform_limit_of_terminal_difference (k : ℕ)
    (hs : Tendsto s atTop atTop)
    (h : ∀ r R z, z ∈ Ω →
      ‖approx Ginv zeta k r z - approx Ginv zeta k (r + R) z‖ ≤
        Real.exp (-s k - 6 * s (k + r))) :
    ∃ f : ComplexVector m → ComplexVector n,
      TendstoUniformlyOn (fun r => approx Ginv zeta k r) f atTop Ω := by
  classical
  have hdecay : Tendsto (fun r => Real.exp (-s k - 6 * s (k + r))) atTop (𝓝 0) := by
    have ht : Tendsto (fun r : ℕ => s (k + r)) atTop atTop := by
      simpa only [Function.comp_def, Nat.add_comm] using hs.comp (tendsto_add_atTop_nat k)
    have he := (exp_decay ht (by norm_num : (0 : ℝ) < 6)).const_mul (Real.exp (-s k))
    simpa only [mul_zero, ← Real.exp_add, sub_eq_add_neg, neg_mul] using he
  have hC : UniformCauchySeqOn (fun r => approx Ginv zeta k r) atTop Ω := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hdecay.eventually (gt_mem_nhds hε))
    refine ⟨N, fun p hp q hq z hz => ?_⟩
    rcases le_total p q with hpq | hqp
    · rw [dist_eq_norm]
      have he : q = p + (q - p) := by omega
      rw [he]
      exact (h p (q - p) z hz).trans_lt (hN p hp)
    · rw [dist_comm, dist_eq_norm]
      have he : p = q + (p - q) := by omega
      rw [he]
      exact (h q (p - q) z hz).trans_lt (hN q hq)
  have hp : ∀ z : Ω, ∃ v : ComplexVector n,
      Tendsto (fun r => approx Ginv zeta k r z) atTop (𝓝 v) := by
    intro z
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hC ε hε
    exact ⟨N, fun p hp q hq => hN p hp q hq z z.2⟩
  choose f hf using hp
  let fext : ComplexVector m → ComplexVector n := fun z =>
    if hz : z ∈ Ω then f ⟨z, hz⟩ else 0
  refine ⟨fext, hC.tendstoUniformlyOn_of_tendsto ?_⟩
  intro z hz
  simpa only [fext, dite_eq_left hz] using hf ⟨z, hz⟩

end Yau.NodeProofs.U01Proof
