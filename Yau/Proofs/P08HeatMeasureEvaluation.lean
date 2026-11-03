import Yau.LeafProofs.L19HeatClassicalCore

/-! The fixed point evaluation of the actual scalar heat as a bounded functional. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold ComplexOrder InnerProductSpace
namespace Yau.NodeProofs.P08Aux.HeatMeasure
open LeafProofs LeafProofs.L19Aux LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private theorem classicalHeat_add (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f k : Lp ℝ 2 μ)
    {t : ℝ} (ht : 0 < t) :
    (fun x => scalarClassicalHeat hn g hK μ hμ (f + k) x t) =
      (fun x => scalarClassicalHeat hn g hK μ hμ f x t +
        scalarClassicalHeat hn g hK μ hμ k x t) := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  apply Measure.eq_of_ae_eq (μ := μ) _
    (continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ (f + k)) ht))
    ((continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ f) ht)).add
      (continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ k) ht)))
  have hp : scalarHeatFamily g μ hμ t (f + k) =
      scalarHeatFamily g μ hμ t f + scalarHeatFamily g μ hμ t k := map_add _ _ _
  filter_upwards [scalarClassicalHeat_ae hn g hK μ hμ (f + k) ht,
    scalarClassicalHeat_ae hn g hK μ hμ f ht, scalarClassicalHeat_ae hn g hK μ hμ k ht,
    Lp.coeFn_add (scalarHeatFamily g μ hμ t f) (scalarHeatFamily g μ hμ t k)] with x hfk hf hk hadd
  simpa only [hp, hadd, Pi.add_apply, hf, hk] using hfk

private theorem classicalHeat_smul (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (c : ℝ) (f : Lp ℝ 2 μ)
    {t : ℝ} (ht : 0 < t) :
    (fun x => scalarClassicalHeat hn g hK μ hμ (c • f) x t) =
      (fun x => c * scalarClassicalHeat hn g hK μ hμ f x t) := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  apply Measure.eq_of_ae_eq (μ := μ) _
    (continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ (c • f)) ht))
    (continuous_const.mul (continuous_of_smoothFn
      (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ f) ht)))
  have hp : scalarHeatFamily g μ hμ t (c • f) = c • scalarHeatFamily g μ hμ t f := map_smul _ _ _
  filter_upwards [scalarClassicalHeat_ae hn g hK μ hμ (c • f) ht,
    scalarClassicalHeat_ae hn g hK μ hμ f ht, Lp.coeFn_smul c (scalarHeatFamily g μ hμ t f)]
    with x hcf hf hsm
  change scalarClassicalHeat hn g hK μ hμ (c • f) x t =
    c * scalarClassicalHeat hn g hK μ hμ f x t
  rw [hcf, hp, hsm, Pi.smul_apply, smul_eq_mul, hf]

private theorem classicalHeat_bound (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ f : Lp ℝ 2 μ, |scalarClassicalHeat hn g hK μ hμ f x t| ≤ C * ‖f‖ := by
  let V := Real.sqrt (μ (distBall g.form x 1)).toReal
  have hV : 0 < V := Real.sqrt_pos.mpr (ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ x zero_lt_one).ne'
    (riemannianVolume_distBall_lt_top g μ hμ x zero_lt_one).ne)
  let C := ((t + 1) / t) ^ n * Real.exp (1 / 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C / V, ?_⟩
  intro f
  have hf : ∀ᵐ y ∂μ, 0 ≤ (|f| : Lp ℝ 2 μ) y := by
    filter_upwards [Lp.coeFn_abs f] with y hy
    rw [hy]
    exact abs_nonneg _
  have hh := nonnegativeHeatRepresentative_point_L2 liYauDifferential g hcomplete hK hRic μ hμ
    (scalarClassicalHeat_smooth hn g hK μ hμ |f|)
    (fun y s hs => scalarClassicalHeat_nonneg hn g hK μ hμ |f| hf y hs)
    (fun y s hs => scalarClassicalHeat_pde hn g hK μ hμ |f| y hs)
    x x t ht (scalarHeatFamily g μ hμ (t + 1) |f|)
    (scalarClassicalHeat_ae hn g hK μ hμ |f| (by linarith)).symm
    univ MeasurableSet.univ (subset_univ _)
  have hind := scalarL2Indicator_norm_le μ univ MeasurableSet.univ
    (scalarHeatFamily g μ hμ (t + 1) |f|)
  have hc := scalarHeatFamily_norm_le g μ hμ (t + 1) |f|
  have hnorm : ‖|f|‖ ≤ ‖f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_abs f] with y hy
    simp only [hy, Real.norm_eq_abs, abs_abs, le_refl]
  have hx : inducedDistance g.form x x = 0 := g.induced_distance_eq_zero.mpr rfl
  simp only [hx, zero_add, one_pow, mul_one] at hh
  have hb : |scalarClassicalHeat hn g hK μ hμ f x t| * V ≤ C * ‖f‖ := by
    calc
      _ ≤ scalarClassicalHeat hn g hK μ hμ |f| x t * V :=
        mul_le_mul_of_nonneg_right (scalarClassicalHeat_abs_le hn g hK μ hμ f x ht) hV.le
      _ ≤ C * ‖scalarL2Indicator μ univ MeasurableSet.univ
          (scalarHeatFamily g μ hμ (t + 1) |f|)‖ := hh
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_left (hind.trans (hc.trans hnorm)) hC
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hV).mpr hb

/-- A point evaluation chosen from the actual classical heat, before its later datum. -/
def heatEvalCLM (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) : Lp ℝ 2 μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => scalarClassicalHeat hn g hK μ hμ f x t
      map_add' := fun f k => congrFun (classicalHeat_add hn g hK μ hμ f k ht) x
      map_smul' := fun c f => congrFun (classicalHeat_smul hn g hK μ hμ c f ht) x }
    (Classical.choose (classicalHeat_bound hn g hcomplete hK hRic μ hμ x t ht))
    (by intro f; exact Classical.choose_spec (classicalHeat_bound hn g hcomplete hK hRic μ hμ x t ht) f)

@[simp] theorem heatEvalCLM_apply (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    heatEvalCLM hn g hcomplete hK hRic μ hμ x t ht f = scalarClassicalHeat hn g hK μ hμ f x t := rfl

/-- The genuine Hilbert Riesz density of fixed heat evaluation. -/
def heatEvalDensity (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) : Lp ℝ 2 μ :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm
    (heatEvalCLM hn g hcomplete hK hRic μ hμ x t ht)

theorem heatEvalDensity_inner (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    inner ℝ (heatEvalDensity hn g hcomplete hK hRic μ hμ x t ht) f =
      scalarClassicalHeat hn g hK μ hμ f x t :=
  InnerProductSpace.toDual_symm_apply

theorem heatEvalDensity_integral (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    (∫ y, heatEvalDensity hn g hcomplete hK hRic μ hμ x t ht y * f y ∂μ) =
      scalarClassicalHeat hn g hK μ hμ f x t := by
  rw [← heatEvalDensity_inner hn g hcomplete hK hRic μ hμ x t ht f, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all μ (fun y => by simp only [RCLike.inner_apply, conj_trivial, mul_comm])

theorem heatEvalDensity_nonneg (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) :
    ∀ᵐ y ∂μ, 0 ≤ heatEvalDensity hn g hcomplete hK hRic μ hμ x t ht y := by
  let e := heatEvalDensity hn g hcomplete hK hRic μ hμ x t ht
  have hneg : ∀ᵐ y ∂μ, 0 ≤ Lp.negPart e y := by
    filter_upwards [Lp.coeFn_negPart e] with y hy
    rw [hy]
    exact neg_nonneg.mpr (min_le_right _ _)
  have hpos := scalarClassicalHeat_nonneg hn g hK μ hμ (Lp.negPart e) hneg x ht
  have heq : inner ℝ e (Lp.negPart e) = -‖Lp.negPart e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_negPart e] with y hy
    simp only [RCLike.inner_apply, conj_trivial, hy]
    rcases le_total (e y) 0 with h | h
    · rw [min_eq_left h]
      ring
    · rw [min_eq_right h]
      ring
  have hz : Lp.negPart e = 0 := by
    have hi : inner ℝ e (Lp.negPart e) = scalarClassicalHeat hn g hK μ hμ (Lp.negPart e) x t :=
      heatEvalDensity_inner hn g hcomplete hK hRic μ hμ x t ht _
    have hn : ‖Lp.negPart e‖ = 0 := by nlinarith [sq_nonneg ‖Lp.negPart e‖]
    exact norm_eq_zero.mp hn
  filter_upwards [Lp.coeFn_negPart e, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with y hy hzero
  rw [hz, hzero] at hy
  have hm : min (e y) 0 = 0 := neg_eq_zero.mp hy.symm
  exact le_of_not_gt (fun h => by rw [min_eq_left h.le] at hm; linarith)

/-- A fixed actual heat measure, independent of all subsequently chosen data. -/
def heatEvalMeasure (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) : Measure M.Carrier :=
  μ.withDensity (fun y => ENNReal.ofReal (heatEvalDensity hn g hcomplete hK hRic μ hμ x t ht y))

theorem heatEvalMeasure_absolutelyContinuous (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) :
    heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht ≪ μ :=
  withDensity_absolutelyContinuous _ _

theorem heatEvalMeasure_integrable (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    Integrable (fun y => f y) (heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) := by
  let e := heatEvalDensity hn g hcomplete hK hRic μ hμ x t ht
  apply (integrable_withDensity_iff_integrable_smul₀'
    (Lp.memLp e).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top))).2
  apply ((Lp.memLp e).integrable_mul (Lp.memLp f)).congr
  filter_upwards [heatEvalDensity_nonneg hn g hcomplete hK hRic μ hμ x t ht] with y hy
  change 0 ≤ e y at hy
  simp only [Pi.mul_apply, ENNReal.toReal_ofReal hy, smul_eq_mul] <;> rfl

theorem heatEvalMeasure_integral (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    (∫ y, f y ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ x t ht) =
      scalarClassicalHeat hn g hK μ hμ f x t := by
  let e := heatEvalDensity hn g hcomplete hK hRic μ hμ x t ht
  rw [heatEvalMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (Lp.memLp e).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top))]
  rw [← heatEvalDensity_integral hn g hcomplete hK hRic μ hμ x t ht f]
  apply integral_congr_ae
  filter_upwards [heatEvalDensity_nonneg hn g hcomplete hK hRic μ hμ x t ht] with y hy
  change 0 ≤ e y at hy
  simp only [Pi.mul_apply, ENNReal.toReal_ofReal hy, smul_eq_mul] <;> rfl

end Yau.NodeProofs.P08Aux.HeatMeasure
