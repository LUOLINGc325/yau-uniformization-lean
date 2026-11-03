import Yau.Proofs.P08HeatMeasureEvaluation

/-! Mass of the actual heat evaluation measure, proved from bounded ball data
and the already proved Gaussian heat comparison. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold ComplexOrder InnerProductSpace
namespace Yau.NodeProofs.P08Aux.HeatMeasure
open LeafProofs LeafProofs.L19Aux LeafProofs.L18Aux LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

variable (hn : 0 < n) (g : SmoothMetric M) (hcomplete : IsComplete g)
  (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
  (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (x : M.Carrier) (t : ℝ) (ht : 0 < t)

include hn hcomplete hK hRic hμ ht

theorem heatEvalMeasure_ball_le_one (r : ℝ) (hr : 0 < r) :
    heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht (distBall g.form x r) ≤ 1 := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht
  let f := scalarBallL2 g μ hμ x r hr
  let B := distBall g.form x r
  have hB : MeasurableSet B := measurableSet_distBall g x r
  have hcoe : (fun y => f y) =ᵐ[ν] B.indicator (fun _ => (1 : ℝ)) :=
    (heatEvalMeasure_absolutelyContinuous hn g hcomplete hK hRic μ hμ x t ht).ae_eq
      (scalarBallL2_coe g μ hμ x r hr)
  have hi := (heatEvalMeasure_integrable hn g hcomplete hK hRic μ hμ x t ht f).congr hcoe
  have hnonneg : ∀ y, 0 ≤ B.indicator (fun _ => (1 : ℝ)) y := fun y =>
    indicator_nonneg (fun _ _ => zero_le_one) _
  have hI : (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂ν) =
      scalarClassicalHeat hn g hK μ hμ f x t := by
    rw [← integral_congr_ae hcoe]
    exact heatEvalMeasure_integral hn g hcomplete hK hRic μ hμ x t ht f
  have hlinf := scalarClassicalHeat_linf hn g hK μ hμ f zero_le_one (by
    filter_upwards [scalarBallL2_coe g μ hμ x r hr] with y hy
    rw [hy]
    by_cases hyB : y ∈ B
    · simp only [B] at hyB
      simp [indicator_of_mem hyB]
    · simp only [B] at hyB
      simp [indicator_of_notMem hyB]) x ht
  calc
    ν B = ∫⁻ y, ENNReal.ofReal (B.indicator (fun _ => (1 : ℝ)) y) ∂ν := by
      have he : (fun y => ENNReal.ofReal (B.indicator (fun _ => (1 : ℝ)) y)) =
          B.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext y
        by_cases hy : y ∈ B <;> simp [hy]
      rw [he, lintegral_indicator hB]
      simp
    _ = ENNReal.ofReal (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂ν) :=
      (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all ν hnonneg)).symm
    _ ≤ 1 := by rw [hI]; exact (ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) hlinf)).trans_eq (by norm_num)

theorem heatEvalMeasure_mass_le :
    heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht univ ≤ 1 := by
  let B : ℕ → Set M.Carrier := fun j => distBall g.form x ((j : ℝ) + 1)
  have hm : Monotone B := by
    intro i j hij y hy
    apply (mem_distBall_iff g x y (by positivity : 0 < (j : ℝ) + 1)).mpr
    have hd := (mem_distBall_iff g x y (by positivity : 0 < (i : ℝ) + 1)).mp hy
    exact hd.trans_le (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hcover : (⋃ j, B j) = univ := by
    ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨j, hj⟩ := exists_nat_gt (inducedDistance g.form x y)
    exact ⟨j, (mem_distBall_iff g x y (by positivity : 0 < (j : ℝ) + 1)).mpr (by linarith)⟩
  have hh := tendsto_measure_iUnion_atTop (μ := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) hm
  rw [hcover] at hh
  apply le_of_tendsto' hh
  intro j
  exact heatEvalMeasure_ball_le_one hn g hcomplete hK hRic μ hμ x t ht _ (by positivity)

/-- Finiteness is established before the mass-one argument. -/
theorem heatEvalMeasure_isFinite :
    IsFiniteMeasure (heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) :=
  ⟨(heatEvalMeasure_mass_le hn g hcomplete hK hRic μ hμ x t ht).trans_lt (by simp)⟩

theorem heatEvalMeasure_gaussian_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (gaussianWeight g x a) (heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) := by
  have hc : (fun y => scalarGaussianL2 g hK hRic μ hμ x a ha y) =ᵐ[
      heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht] gaussianWeight g x a := by
    filter_upwards [(heatEvalMeasure_absolutelyContinuous hn g hcomplete hK hRic μ hμ x t ht).ae_eq
      (scalarGaussianL2_coe g hK hRic μ hμ x a ha)] with y hy
    change _ = Real.exp (-(a * inducedDistance g.form x y ^ 2))
    rw [hy]
    congr 1
    ring
  exact (heatEvalMeasure_integrable hn g hcomplete hK hRic μ hμ x t ht
    (scalarGaussianL2 g hK hRic μ hμ x a ha)).congr hc

theorem heatEvalMeasure_gaussian_lower {a : ℝ} (ha : 0 < a) :
    Real.exp (-((2 * n : ℕ) * a * t)) ≤
      ∫ y, gaussianWeight g x a y ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht := by
  have hc : (fun y => scalarGaussianL2 g hK hRic μ hμ x a ha y) =ᵐ[
      heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht] gaussianWeight g x a := by
    filter_upwards [(heatEvalMeasure_absolutelyContinuous hn g hcomplete hK hRic μ hμ x t ht).ae_eq
      (scalarGaussianL2_coe g hK hRic μ hμ x a ha)] with y hy
    change _ = Real.exp (-(a * inducedDistance g.form x y ^ 2))
    rw [hy]
    congr 1
    ring
  rw [← integral_congr_ae hc, heatEvalMeasure_integral]
  have hh := scalarClassicalGaussianHeat_lower hn g hK hRic μ hμ x ha x ht
  have hzero : gaussianWeight g x a x = 1 := by
    simp only [gaussianWeight, g.induced_distance_eq_zero.mpr rfl, zero_pow (by decide : 2 ≠ 0),
      mul_zero, neg_zero, Real.exp_zero]
  simpa only [hzero, mul_one] using hh

/-- The true heat evaluation is a probability measure; no kernel or mass premise is used. -/
theorem heatEvalMeasure_mass :
    heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht univ = 1 := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ x t ht
  have hl (a : ℝ) (ha : 0 < a) : Real.exp (-((2 * n : ℕ) * a * t)) ≤ (ν univ).toReal := by
    have hbound : ∀ y, gaussianWeight g x a y ≤ 1 := by
      intro y
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg ha.le (sq_nonneg _))
    calc
      _ ≤ ∫ y, gaussianWeight g x a y ∂ν := heatEvalMeasure_gaussian_lower hn g hcomplete hK hRic μ hμ x t ht ha
      _ ≤ ∫ _ : M.Carrier, (1 : ℝ) ∂ν := integral_mono
        (heatEvalMeasure_gaussian_integrable hn g hcomplete hK hRic μ hμ x t ht ha)
        (integrable_const 1) hbound
      _ = (ν univ).toReal := by simp only [integral_const, smul_eq_mul, mul_one, Measure.real]
  have hlim : Tendsto (fun j : ℕ => Real.exp (-((2 * n : ℕ) * (1 / ((j : ℝ) + 1)) * t)))
      atTop (𝓝 (1 : ℝ)) := by
    have h := (((tendsto_const_nhds (x := ((2 * n : ℕ) : ℝ))).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const t).neg
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp h
  have hreal : 1 ≤ (ν univ).toReal := le_of_tendsto' hlim (fun j => hl _ (by positivity))
  apply le_antisymm (heatEvalMeasure_mass_le hn g hcomplete hK hRic μ hμ x t ht)
  simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν univ)).2 hreal

end Yau.NodeProofs.P08Aux.HeatMeasure
