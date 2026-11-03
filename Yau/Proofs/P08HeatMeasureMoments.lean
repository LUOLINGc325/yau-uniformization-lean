import Yau.Proofs.P08HeatMeasureMass

/-! Moments of the actual evaluation measure, derived from Gaussian comparison. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold ComplexOrder InnerProductSpace
namespace Yau.NodeProofs.P08Aux.HeatMeasure
open LeafProofs LeafProofs.L19Aux LeafProofs.L18Aux LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private theorem gaussian_difference_quotient_tendsto (q : ℝ) :
    Tendsto (fun j : ℕ => (1 - Real.exp (-((1 / ((j : ℝ) + 1)) * q))) /
      (1 / ((j : ℝ) + 1))) atTop (𝓝 q) := by
  have hd : HasDerivAt (fun a : ℝ => 1 - Real.exp (-(a * q))) q 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      (((hasDerivAt_id (0 : ℝ)).mul_const q).neg.exp) using 1 <;> simp <;> rfl
  have hseq : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun j => by change 0 < 1 / ((j : ℝ) + 1); positivity)⟩
  simpa only [Function.comp_def, zero_add, zero_mul, neg_zero, Real.exp_zero, sub_self,
    sub_zero, smul_eq_mul, div_eq_mul_inv, mul_zero, mul_comm] using hd.tendsto_slope_zero_right.comp hseq

variable (hn : 0 < n) (g : SmoothMetric M) (hcomplete : IsComplete g)
  (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
  (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (x : M.Carrier) (t : ℝ) (ht : 0 < t)
include hn hcomplete hK hRic hμ ht

private theorem gaussian_difference_integral_le {a : ℝ} (ha : 0 < a) :
    (∫ y, (1 - gaussianWeight g x a y) / a
      ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) ≤ (2 * n : ℕ) * t := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ x t ht
  have hmass : ν univ = 1 := heatEvalMeasure_mass hn g hcomplete hK hRic μ hμ x t ht
  have hi := heatEvalMeasure_gaussian_integrable hn g hcomplete hK hRic μ hμ x t ht ha
  have hlow := heatEvalMeasure_gaussian_lower hn g hcomplete hK hRic μ hμ x t ht ha
  rw [integral_div, integral_sub (integrable_const 1) hi]
  have hconst : (∫ _ : M.Carrier, (1 : ℝ) ∂ν) = 1 := by simp [integral_const, Measure.real, hmass]
  rw [hconst]
  apply (div_le_iff₀ ha).mpr
  have he := Real.add_one_le_exp (-((2 * n : ℕ) * a * t))
  nlinarith

/-- The genuine finite second moment; its constant is derived from the true Gaussian comparison. -/
theorem heatEvalMeasure_secondMoment :
    (∫⁻ y, ENNReal.ofReal (distFrom g.form x y ^ 2)
      ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) ≤ ENNReal.ofReal ((2 * n : ℕ) * t) := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht
  let a : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let F : ℕ → M.Carrier → ℝ := fun j y => (1 - gaussianWeight g x (a j) y) / a j
  have ha (j : ℕ) : 0 < a j := by dsimp [a]; positivity
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ x t ht
  have hFm (j : ℕ) : Measurable (F j) := by
    exact (measurable_const.sub (gaussianWeight_continuous g x (a j)).measurable).div_const _
  have hFn (j : ℕ) (y : M.Carrier) : 0 ≤ F j y := by
    apply div_nonneg _ (ha j).le
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (ha j).le (sq_nonneg _)))
  have hFi (j : ℕ) : Integrable (F j) ν :=
    ((integrable_const 1).sub (heatEvalMeasure_gaussian_integrable hn g hcomplete hK hRic μ hμ x t ht (ha j))).div_const _
  have hbound (j : ℕ) : (∫⁻ y, ENNReal.ofReal (F j y) ∂ν) ≤ ENNReal.ofReal ((2 * n : ℕ) * t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi j) (ae_of_all ν (hFn j))]
    exact ENNReal.ofReal_le_ofReal (gaussian_difference_integral_le hn g hcomplete hK hRic μ hμ x t ht (ha j))
  have hlim (y : M.Carrier) : Tendsto (fun j => ENNReal.ofReal (F j y)) atTop
      (𝓝 (ENNReal.ofReal (distFrom g.form x y ^ 2))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [F, a, gaussianWeight, distFrom] using gaussian_difference_quotient_tendsto (inducedDistance g.form x y ^ 2)
  calc
    _ = ∫⁻ y, liminf (fun j => ENNReal.ofReal (F j y)) atTop ∂ν := by
      apply lintegral_congr
      intro y
      exact (hlim y).liminf_eq.symm
    _ ≤ liminf (fun j => ∫⁻ y, ENNReal.ofReal (F j y) ∂ν) atTop :=
      lintegral_liminf_le (fun j => (hFm j).ennreal_ofReal)
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently

theorem heatEvalMeasure_integrable_sq_distance :
    Integrable (fun y => distFrom g.form x y ^ 2)
      (heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((continuous_distFrom g x).pow 2).aestronglyMeasurable (ae_of_all _ (fun y => sq_nonneg _))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (heatEvalMeasure_secondMoment hn g hcomplete hK hRic μ hμ x t ht)

theorem heatEvalMeasure_integrable_distance :
    Integrable (distFrom g.form x) (heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ x t ht
  apply ((integrable_const (1 : ℝ)).add
    (heatEvalMeasure_integrable_sq_distance hn g hcomplete hK hRic μ hμ x t ht)).mono'
    (continuous_distFrom g x).aestronglyMeasurable
  apply ae_of_all
  intro y
  change |distFrom g.form x y| ≤ 1 + distFrom g.form x y ^ 2
  rw [abs_of_nonneg (show 0 ≤ distFrom g.form x y from g.induced_distance_nonneg x y)]
  nlinarith [sq_nonneg (distFrom g.form x y - 1)]

/-- Cauchy--Schwarz for this probability measure, proved by its nonnegative variance. -/
theorem heatEvalMeasure_firstMoment :
    (∫ y, distFrom g.form x y ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) ≤
      Real.sqrt ((2 * n : ℕ) * t) := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ x t ht
  let m := ∫ y, distFrom g.form x y ∂ν
  have hi := heatEvalMeasure_integrable_distance hn g hcomplete hK hRic μ hμ x t ht
  have hi2 := heatEvalMeasure_integrable_sq_distance hn g hcomplete hK hRic μ hμ x t ht
  have hmass : ν univ = 1 := heatEvalMeasure_mass hn g hcomplete hK hRic μ hμ x t ht
  have hpoly : (∫ y, (distFrom g.form x y - m) ^ 2 ∂ν) =
      (∫ y, distFrom g.form x y ^ 2 ∂ν) - m ^ 2 := by
    have he : (fun y => (distFrom g.form x y - m) ^ 2) =
        fun y => (distFrom g.form x y ^ 2 - (2 * m) * distFrom g.form x y) + m ^ 2 := by
      funext y
      ring
    rw [he, integral_add (f := fun y => distFrom g.form x y ^ 2 - (2 * m) * distFrom g.form x y)
      (g := fun _ => m ^ 2) (hi2.sub (hi.const_mul (2 * m))) (integrable_const (m ^ 2)),
      integral_sub (f := fun y => distFrom g.form x y ^ 2)
        (g := fun y => (2 * m) * distFrom g.form x y) hi2 (hi.const_mul (2 * m)),
      integral_const_mul, integral_const]
    simp only [Measure.real, hmass, ENNReal.toReal_one, one_smul]
    change _ - 2 * m * m + m ^ 2 = _
    ring
  have hv : m ^ 2 ≤ ∫ y, distFrom g.form x y ^ 2 ∂ν := by
    have hh : (0 : ℝ) ≤ ∫ y, (distFrom g.form x y - m) ^ 2 ∂ν :=
      integral_nonneg (fun y => sq_nonneg (distFrom g.form x y - m))
    rw [hpoly] at hh
    linarith
  have hsecond : (∫ y, distFrom g.form x y ^ 2 ∂ν) ≤ (2 * n : ℕ) * t := by
    have hh := heatEvalMeasure_secondMoment hn g hcomplete hK hRic μ hμ x t ht
    rw [← ofReal_integral_eq_lintegral_ofReal hi2 (ae_of_all ν (fun y => sq_nonneg _))] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ (2 * n : ℕ) * t)).mp hh
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 * n : ℕ) * t)
  change m ≤ _
  nlinarith [Real.sqrt_nonneg (((2 * n : ℕ) : ℝ) * t)]

/-- Every measurable scalar of at most linear absolute growth is integrable. -/
theorem heatEvalMeasure_integrable_linear {f : M.Carrier → ℝ} {B A : ℝ}
    (hf : AEStronglyMeasurable f (heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht))
    (hbound : ∀ y, |f y| ≤ B + A * distFrom g.form x y) :
    Integrable f (heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ x t ht
  apply ((integrable_const B).add
    ((heatEvalMeasure_integrable_distance hn g hcomplete hK hRic μ hμ x t ht).const_mul A)).mono' hf
  exact ae_of_all ν (fun y => by change |f y| ≤ B + A * distFrom g.form x y; exact hbound y)

end Yau.NodeProofs.P08Aux.HeatMeasure
