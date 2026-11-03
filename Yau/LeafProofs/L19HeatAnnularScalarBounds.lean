import Yau.LeafProofs.L19HeatDualBoundaryTime

/-! Gaussian domination of actual compact-region squared scalar integrals. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

/-- The squared Gaussian bound with its displayed exponent. -/
theorem sq_le_exp_twice_of_abs_le {f C e : ℝ} (_hC : 0 ≤ C)
    (hf : |f| ≤ C * Real.exp e) : f ^ 2 ≤ C ^ 2 * Real.exp (2 * e) := by
  calc
    f ^ 2 = |f| ^ 2 := (sq_abs f).symm
    _ ≤ (C * Real.exp e) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hf _
    _ = C ^ 2 * Real.exp (2 * e) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num

/-- A genuine Gaussian upper bound on a compact region can be integrated
against the original Riemannian measure; its total Gaussian integral is finite. -/
theorem integralOn_sq_le_gaussian_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a D : ℝ} (ha : 0 < a)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) {K : Set M.Carrier} (hcompact : IsCompact K)
    (hD : 0 ≤ D) (hbound : ∀ x ∈ K, f x ^ 2 ≤ D * gaussianWeight g o a x) :
    (∫ x in K, f x ^ 2 ∂μ) ≤ D * ∫ x, gaussianWeight g o a x ∂μ := by
  have hf2 := smoothFn_integrableOn_compact g μ hμ (smoothFn_pow hf 2) hcompact
  have hi : Integrable (gaussianWeight g o a) μ := by
    change Integrable (fun x => Real.exp (-(a * inducedDistance g.form o x ^ 2))) μ
    simpa only [neg_mul] using integrable_exp_neg_distance_sq g hK hRic μ hμ o ha
  calc
    _ ≤ ∫ x in K, D * gaussianWeight g o a x ∂μ :=
      setIntegral_mono_on hf2 (hi.const_mul D).integrableOn hcompact.measurableSet hbound
    _ ≤ ∫ x, D * gaussianWeight g o a x ∂μ :=
      setIntegral_le_integral (hi.const_mul D)
        (ae_of_all _ fun x => mul_nonneg hD (gaussianWeight_pos g o a x).le)
    _ = _ := integral_const_mul _ _

/-- Arbitrarily small Gaussian growth bounds squared scalars on a bounded
annulus without a separate polynomial volume estimate. -/
theorem integralOn_sq_gaussian_growth_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a C L : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (_hL : 0 ≤ L) {f : M.Carrier → ℝ} (hf : SmoothFn f)
    {K : Set M.Carrier} (hcompact : IsCompact K)
    (hbounded : ∀ x ∈ K, inducedDistance g.form o x ≤ L)
    (hbound : ∀ x, |f x| ≤ C * Real.exp (a * inducedDistance g.form o x ^ 2)) :
    (∫ x in K, f x ^ 2 ∂μ) ≤
      (C ^ 2 * Real.exp (3 * a * L ^ 2)) * ∫ x, gaussianWeight g o a x ∂μ := by
  apply integralOn_sq_le_gaussian_bound g hK hRic μ hμ o ha hf hcompact (by positivity)
  intro x hx
  have hs := pow_le_pow_left₀ (g.induced_distance_nonneg o x) (hbounded x hx) 2
  have he : 2 * (a * inducedDistance g.form o x ^ 2) ≤
      3 * a * L ^ 2 - a * inducedDistance g.form o x ^ 2 := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hs)]
  calc
    _ ≤ C ^ 2 * Real.exp (2 * (a * inducedDistance g.form o x ^ 2)) :=
      sq_le_exp_twice_of_abs_le hC (hbound x)
    _ ≤ C ^ 2 * Real.exp (3 * a * L ^ 2 - a * inducedDistance g.form o x ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
    _ = _ := by
      dsimp only [gaussianWeight]
      rw [sub_eq_add_neg, Real.exp_add]
      ring

/-- A pointwise Gaussian tail gives an actual squared-scalar integral
tail beyond each inner annular radius, with the original volume. -/
theorem integralOn_sq_gaussian_decay_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a C l : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hl : 0 ≤ l) {f : M.Carrier → ℝ} (hf : SmoothFn f)
    {K : Set M.Carrier} (hcompact : IsCompact K)
    (hfar : ∀ x ∈ K, l ≤ inducedDistance g.form o x)
    (hbound : ∀ x, |f x| ≤ C * Real.exp (-a * inducedDistance g.form o x ^ 2)) :
    (∫ x in K, f x ^ 2 ∂μ) ≤
      (C ^ 2 * Real.exp (-a * l ^ 2)) * ∫ x, gaussianWeight g o a x ∂μ := by
  apply integralOn_sq_le_gaussian_bound g hK hRic μ hμ o ha hf hcompact (by positivity)
  intro x hx
  have hs := pow_le_pow_left₀ hl (hfar x hx) 2
  have he : 2 * (-a * inducedDistance g.form o x ^ 2) ≤
      -a * l ^ 2 - a * inducedDistance g.form o x ^ 2 := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hs)]
  calc
    _ ≤ C ^ 2 * Real.exp (2 * (-a * inducedDistance g.form o x ^ 2)) :=
      sq_le_exp_twice_of_abs_le hC (hbound x)
    _ ≤ C ^ 2 * Real.exp (-a * l ^ 2 - a * inducedDistance g.form o x ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
    _ = _ := by
      dsimp only [gaussianWeight]
      rw [sub_eq_add_neg, Real.exp_add]
      simp only [neg_mul]
      ring

end Yau.LeafProofs.L19Aux
