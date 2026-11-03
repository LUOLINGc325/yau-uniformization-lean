import Yau.Proofs.V01ClosedWitness
import Yau.Proofs.V05Matrix

/-! V01 scratch source. The published V05 trace-product theorem is reused;
its source/native eligibility must be supplied by the dedicated receiver. -/

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

/-- The transpose is retained from the tangent-cotangent pairing. -/
theorem coercive_trace_bound {C S : Herm n} {c : ℝ}
    (hC : (C - (c : ℂ) • (1 : Herm n)).PosSemidef) (hS : S.PosSemidef) :
    c * S.trace.re ≤ (Cᵀ * S).trace.re := by
  have hp := (Complex.nonneg_iff.mp
    (Yau.NodeProofs.V05Aux.trace_mul_nonneg hC.transpose hS)).1
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hp
  linarith

theorem eventually_trace_bounded_of_coercive_cost
    (C S : ℕ → Herm n) (τ c : ℝ) (hc : 0 < c)
    (hS : ∀ᶠ m in atTop, (S m).PosSemidef)
    (hC : ∀ᶠ m in atTop, (C m - (c : ℂ) • (1 : Herm n)).PosSemidef)
    (hcost : SeqUpperZero (fun m => ((C m)ᵀ * S m).trace.re - τ)) :
    ∀ᶠ m in atTop, (S m).PosSemidef ∧
      (S m).trace.re ≤ (|τ| + 2) / c := by
  filter_upwards [hS, hC, hcost 1 zero_lt_one] with m hmS hmC hmCost
  refine ⟨hmS, (le_div_iff₀ hc).mpr ?_⟩
  have hcoerc := coercive_trace_bound hmC hmS
  nlinarith [le_abs_self τ]

theorem closed_psd_witness_of_coercive_cost
    (S C B : ℕ → Herm n) (C₀ B₀ : Herm n) (τ c : ℝ) (hc : 0 < c)
    (hC : Tendsto C atTop (𝓝 C₀)) (hB : Tendsto B atTop (𝓝 B₀))
    (hS : ∀ᶠ m in atTop, (S m).PosSemidef)
    (hSB : ∀ᶠ m in atTop, (S m - B m).PosSemidef)
    (hCbound : ∀ᶠ m in atTop, (C m - (c : ℂ) • (1 : Herm n)).PosSemidef)
    (hcost : SeqUpperZero (fun m => ((C m)ᵀ * S m).trace.re - τ)) :
    ∃ K : Herm n, K.PosSemidef ∧ (K - B₀).PosSemidef ∧
      (C₀ᵀ * K).trace.re ≤ τ :=
  closed_psd_witness_of_trace_bound S C B C₀ B₀ τ ((|τ| + 2) / c) hC hB
    (eventually_trace_bounded_of_coercive_cost C S τ c hc hS hCbound hcost) hSB hcost

end Yau.Blueprint.V01Proof
