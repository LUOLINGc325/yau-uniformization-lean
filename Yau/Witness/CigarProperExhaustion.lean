import Yau.LeafProofs.L23FieldMetric

open scoped Topology

noncomputable section

namespace Yau.Witness.Cigar

/-- A smooth Hermitian length distance is complete when it bounds the
oscillation of an exhaustion with compact sublevels. -/
theorem completeDistance_of_compact_sublevels
    {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h)
    (F : M.Carrier → ℝ)
    (hcompact : ∀ B : ℝ, IsCompact {z | F z ≤ B})
    (hbound : ∀ x y, |F x - F y| ≤ inducedDistance h x y) :
    IsCompleteDistance (inducedDistance h) := by
  letI := Yau.LeafProofs.L23Aux.metricSpaceOfField h hs
  letI : ProperSpace M.Carrier := by
    constructor
    intro x R
    apply (hcompact (F x + R)).of_isClosed_subset Metric.isClosed_closedBall
    intro y hy
    have hd : inducedDistance h y x ≤ R := hy
    have hb := hbound y x
    have ha := le_abs_self (F y - F x)
    change F y ≤ F x + R
    linarith
  intro s hsC
  have hc : CauchySeq s := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hsC ε hε
    exact ⟨N, fun m hm k hk => hN m k hm hk⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx ε hε
  exact ⟨N, fun k hk => hN k hk⟩

section LogNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The smooth logarithmic exhaustion of a real inner product space. -/
theorem logNorm_hasFDerivAt (z : E) :
    HasFDerivAt (fun p : E => Real.log (1 + ‖p‖ ^ 2) / 2)
      ((1 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have hq : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).log hq).const_smul (1 / 2 : ℝ)
  convert h using 1 <;> ext w <;>
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring

/-- Its derivative is dominated by the conformal cigar norm. -/
theorem logNorm_derivative_bound (z w : E) :
    |inner ℝ z w / (1 + ‖z‖ ^ 2)| ≤
      ‖w‖ / Real.sqrt (1 + ‖z‖ ^ 2) := by
  have hq : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.2 hq
  have hz : ‖z‖ ≤ Real.sqrt (1 + ‖z‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by linarith)
  calc
    |inner ℝ z w / (1 + ‖z‖ ^ 2)| =
        |inner ℝ z w| / (1 + ‖z‖ ^ 2) := by rw [abs_div, abs_of_pos hq]
    _ ≤ (‖z‖ * ‖w‖) / (1 + ‖z‖ ^ 2) :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm z w) hq.le
    _ ≤ (Real.sqrt (1 + ‖z‖ ^ 2) * ‖w‖) / (1 + ‖z‖ ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) hq.le
    _ = ‖w‖ / Real.sqrt (1 + ‖z‖ ^ 2) := by
      have hsq := Real.sq_sqrt hq.le
      apply (div_eq_div_iff (ne_of_gt hq) (ne_of_gt hs)).2
      calc
        Real.sqrt (1 + ‖z‖ ^ 2) * ‖w‖ * Real.sqrt (1 + ‖z‖ ^ 2) =
            ‖w‖ * Real.sqrt (1 + ‖z‖ ^ 2) ^ 2 := by ring
        _ = _ := by rw [hsq]

/-- Logarithmic norm sublevels are compact in the original norm topology. -/
theorem logNorm_sublevel_compact [ProperSpace E] (B : ℝ) :
    IsCompact {z : E | Real.log (1 + ‖z‖ ^ 2) / 2 ≤ B} := by
  have hc : Continuous (fun z : E => Real.log (1 + ‖z‖ ^ 2) / 2) :=
    continuous_iff_continuousAt.2 fun z => (logNorm_hasFDerivAt z).continuousAt
  apply (isCompact_closedBall (0 : E) (Real.exp B)).of_isClosed_subset
    (isClosed_le hc continuous_const)
  intro z hz
  change dist z 0 ≤ Real.exp B
  rw [dist_zero_right]
  have hlog : Real.log (1 + ‖z‖ ^ 2) ≤ B + B := by
    change Real.log (1 + ‖z‖ ^ 2) / 2 ≤ B at hz
    linarith
  have he : 1 + ‖z‖ ^ 2 ≤ Real.exp B ^ 2 := by
    calc
      1 + ‖z‖ ^ 2 = Real.exp (Real.log (1 + ‖z‖ ^ 2)) :=
        (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (B + B) := Real.exp_le_exp.2 hlog
      _ = Real.exp B ^ 2 := by rw [Real.exp_add, pow_two]
  apply (sq_le_sq₀ (norm_nonneg z) (Real.exp_pos B).le).1
  linarith

end LogNorm

end Yau.Witness.Cigar
