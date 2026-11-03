import Yau.LeafProofs.L03CompletionFiber

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

theorem ae_summable_sqrt_of_fast_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q : ℕ → X → ℝ)
    (hq : ∀ j x, 0 ≤ q j x) (hm : ∀ j, AEStronglyMeasurable (q j) μ)
    (hb : ∀ j, (∫⁻ x, ENNReal.ofReal (q j x) ∂μ) ≤ ENNReal.ofReal ((1 / 16 : ℝ) ^ j)) :
    ∀ᵐ x ∂μ, Summable (fun j => Real.sqrt (q j x)) := by
  let E := fun j => {x | ENNReal.ofReal ((1 / 4 : ℝ) ^ j) ≤ ENNReal.ofReal (q j x)}
  have hE (j : ℕ) : μ (E j) ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ j) := by
    have hp : 0 < (1 / 4 : ℝ) ^ j := by positivity
    have hn : ENNReal.ofReal ((1 / 4 : ℝ) ^ j) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
    have hmark := meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp_aemeasurable (hm j).aemeasurable)
      hn ENNReal.ofReal_ne_top
    calc
      μ (E j) ≤ (∫⁻ x, ENNReal.ofReal (q j x) ∂μ) / ENNReal.ofReal ((1 / 4 : ℝ) ^ j) := hmark
      _ ≤ ENNReal.ofReal ((1 / 16 : ℝ) ^ j) / ENNReal.ofReal ((1 / 4 : ℝ) ^ j) := by gcongr; exact hb j
      _ = ENNReal.ofReal ((1 / 4 : ℝ) ^ j) := by
        rw [← ENNReal.ofReal_div_of_pos hp, ← div_pow]
        norm_num
  have hgeo : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hs : (∑' j, μ (E j)) ≠ ⊤ := by
    apply ne_of_lt
    apply (ENNReal.tsum_le_tsum hE).trans_lt
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hgeo]
    exact ENNReal.ofReal_lt_top
  filter_upwards [ae_eventually_notMem hs] with x hx
  apply summable_geometric_two.of_norm_bounded_eventually_nat
  filter_upwards [hx] with j hj
  have hlt : q j x < (1 / 4 : ℝ) ^ j := by
    have he : ENNReal.ofReal (q j x) < ENNReal.ofReal ((1 / 4 : ℝ) ^ j) := not_le.mp hj
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp he
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  calc
    q j x ≤ (1 / 4 : ℝ) ^ j := hlt.le
    _ = ((1 / 2 : ℝ) ^ j) ^ 2 := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num

variable {n k : ℕ} {M : ComplexManifold n}

/-- A sufficiently fast Cauchy sequence of actual sections has an
almost everywhere limit in the actual alternating tangent fibres.
The good AE set is global and uses the intrinsic metric norm. -/
theorem exists_ae_fiber_limit_of_fast_realize
    (g : SmoothMetric M) (μ : Measure M.Carrier) (u : ℕ → L2FormSpace g μ k)
    (hstep : ∀ j, ‖realizeL2Form g μ (u (j + 1)) - realizeL2Form g μ (u j)‖ ≤ (1 / 4 : ℝ) ^ j) :
    ∃ A : RealForm M k, ∀ᵐ x ∂μ, Tendsto (fun j => (u j).toSection x) atTop (𝓝 (A x)) := by
  classical
  let q := fun j => formNormSq g.form (u (j + 1) - u j).toSection
  have hq (j : ℕ) (x : M.Carrier) : 0 ≤ q j x := formNormSq_nonneg g.form _ x
  have hm (j : ℕ) : AEStronglyMeasurable (q j) μ :=
    formNormSq_aestronglyMeasurable g μ _ (u (j + 1) - u j).toSection_l2
  have hb (j : ℕ) : (∫⁻ x, ENNReal.ofReal (q j x) ∂μ) ≤ ENNReal.ofReal ((1 / 16 : ℝ) ^ j) := by
    have hI := ofReal_integral_eq_lintegral_ofReal
      (formNormSq_integrable g μ _ (u (j + 1) - u j).toSection_l2)
      (Eventually.of_forall (hq j))
    rw [← hI, ← realizeL2Form_norm_sq, realizeL2Form_sub]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((1 / 4 : ℝ) ^ j) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hstep j)
      _ = (1 / 16 : ℝ) ^ j := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have hsum := ae_summable_sqrt_of_fast_lintegral μ q hq hm hb
  have hex (x : M.Carrier) (hx : Summable (fun j => Real.sqrt (q j x))) :
      ∃ P : (TangentVector M x)[⋀^Fin k]→L[ℝ] ℝ,
        Tendsto (fun j => (u j).toSection x) atTop (𝓝 P) := by
    have hc (I : Fin k → RIdx n) : ∃ a : ℝ,
        Tendsto (fun j => formComponents (u j).toSection x (chartPt x x) I) atTop (𝓝 a) := by
      obtain ⟨C, hC, hCI⟩ := center_coefficient_abs_le_metric g.form x I
      apply cauchySeq_tendsto_of_complete
      apply cauchySeq_of_dist_le_of_summable (fun j => C * Real.sqrt (q j x)) _ (hx.mul_left C)
      intro j
      have he : formComponents (u (j + 1) - u j).toSection x (chartPt x x) I =
          formComponents (u (j + 1)).toSection x (chartPt x x) I -
            formComponents (u j).toSection x (chartPt x x) I := by
        rw [L2FormSpace.toSection_sub]
        rfl
      rw [dist_comm, Real.dist_eq, ← he]
      exact hCI _
    choose a ha using hc
    refine ⟨centerFormReconstruction x a, ?_⟩
    have ht := (centerFormReconstruction (k := k) x).continuous.tendsto a |>.comp (tendsto_pi_nhds.mpr ha)
    simpa only [Function.comp_def, centerFormReconstruction_coeff] using ht
  let A : RealForm M k := fun x => if h : ∃ P : (TangentVector M x)[⋀^Fin k]→L[ℝ] ℝ,
    Tendsto (fun j => (u j).toSection x) atTop (𝓝 P) then h.choose else 0
  refine ⟨A, ?_⟩
  filter_upwards [hsum] with x hx
  have h := hex x hx
  exact (show A x = h.choose by simp only [A, dif_pos h]) ▸ h.choose_spec

end Yau.LeafProofs.L03
