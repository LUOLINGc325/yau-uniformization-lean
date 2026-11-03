import Yau.LeafProofs.L19HeatFamilyDerivative
import Yau.LeafProofs.L19ScalarMarkovBounds

/-! The actual compact scalar generator and its heat evolution. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem scalarEnergyL2_adjoint_greenTest (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) :
    (scalarEnergyL2 g μ hμ).adjoint
      (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)) =
      (k : ScalarEnergySpace g μ hμ) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hG := scalarEnergyL2_green g hK μ hμ v k
  have hcomm : ⟪v, (k : ScalarEnergySpace g μ hμ)⟫_ℝ =
      ⟪(k : ScalarEnergySpace g μ hμ), v⟫_ℝ := real_inner_comm _ _
  have hcomm' : ⟪scalarEnergyL2 g μ hμ v,
      scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)⟫_ℝ =
      ⟪scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k), scalarEnergyL2 g μ hμ v⟫_ℝ :=
    real_inner_comm _ _
  linarith only [hG, hcomm, hcomm']

def scalarCompactLaplacian (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ScalarEnergyDomain g μ hμ) :
    ScalarEnergyDomain g μ hμ :=
  ⟨laplacian g.form k, smoothFn_laplacian g k.2.1,
    laplacian_hasCompactSupport g.form k.2.1 k.2.2⟩

theorem scalarEnergyGreenTest_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ScalarEnergyDomain g μ hμ) :
    scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k) =
      scalarEnergyDomainL2 g μ hμ k -
        scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k) := by
  apply Lp.ext
  filter_upwards [scalarEnergyDomainL2_coe g μ hμ (scalarEnergyGreenTest g μ hμ k),
    scalarEnergyDomainL2_coe g μ hμ k,
    scalarEnergyDomainL2_coe g μ hμ (scalarCompactLaplacian g μ hμ k),
    Lp.coeFn_sub (scalarEnergyDomainL2 g μ hμ k)
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))] with y hG hk hL hs
  rw [hG, hs, Pi.sub_apply, hk, hL]
  rfl

theorem scalarResolvent_compact_generator (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) :
    scalarResolvent g μ hμ 1 zero_lt_one
      (scalarEnergyDomainL2 g μ hμ k - scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k)) =
      scalarEnergyDomainL2 g μ hμ k := by
  rw [← scalarEnergyGreenTest_L2, scalarResolvent_one_eq]
  change scalarEnergyL2 g μ hμ ((scalarEnergyL2 g μ hμ).adjoint
    (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k))) = _
  rw [scalarEnergyL2_adjoint_greenTest g hK, scalarEnergyL2_coe]

theorem scalarComplexHeat_right_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    scalarComplexHeatInverse g μ hμ t * scalarComplexResolvent g μ hμ =
      scalarComplexHeat g μ hμ t := by
  rw [scalarComplexHeat_factor g μ hμ ht]
  exact ((Commute.refl (scalarComplexResolvent g μ hμ)).cfc_real (scalarHeatInverseMultiplier t)).eq

theorem scalarHeatFamily_right_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    scalarHeatInverse g μ hμ t * scalarResolvent g μ hμ 1 zero_lt_one = scalarHeatFamily g μ hμ t := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Function.LeftInverse.injective (heatLpRe_ofReal μ))
  rw [mul_apply_eq_comp, scalarHeatInverse_ofReal g μ hμ ht,
    ← scalarComplexResolvent_ofReal, scalarHeatFamily_ofReal,
    ← mul_apply_eq_comp, scalarComplexHeat_right_factor g μ hμ ht]

/-- Every actual smooth compact scalar lies in the true heat generator
domain, and the generator is its computed project Laplacian. -/
theorem scalarHeat_compact_hasDerivAt (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => scalarHeatFamily g μ hμ s (scalarEnergyDomainL2 g μ hμ k))
      (scalarHeatFamily g μ hμ t
        (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))) t := by
  have hd := scalarHeatFamily_apply_hasDerivAt g μ hμ ht (scalarEnergyDomainL2 g μ hμ k)
  have hR := scalarResolvent_compact_generator g hK μ hμ k
  have hIR : scalarHeatInverse g μ hμ t (scalarEnergyDomainL2 g μ hμ k) =
      scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ k -
        scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k)) := by
    conv_lhs => rw [← hR]
    exact congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A
      (scalarEnergyDomainL2 g μ hμ k - scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k)))
        (scalarHeatFamily_right_factor g μ hμ ht)
  rw [hIR, map_sub] at hd
  convert hd using 1 <;> abel

theorem scalarHeatFamily_continuousOn_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    ContinuousOn (fun t => scalarHeatFamily g μ hμ t f) (Set.Ici 0) := by
  intro t ht
  have ht0 : 0 ≤ t := ht
  rcases ht0.eq_or_lt with rfl | ht
  · simpa only [ContinuousWithinAt, scalarHeatFamily_zero, one_apply_eq_self] using
      scalarHeatFamily_tendsto_zero g μ hμ f
  · exact (scalarHeatFamily_apply_hasDerivAt g μ hμ ht f).continuousAt.continuousWithinAt

/-- The original smooth compact scalar has the actual Bochner-valued
Duhamel formula, with its computed Laplacian and genuine initial value. -/
theorem scalarHeat_compact_duhamel (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) {T : ℝ} (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, scalarHeatFamily g μ hμ s
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))) =
      scalarHeatFamily g μ hμ T (scalarEnergyDomainL2 g μ hμ k) - scalarEnergyDomainL2 g μ hμ k := by
  have hcont : ContinuousOn (fun t => scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ k))
      (Set.Icc 0 T) := (scalarHeatFamily_continuousOn_nonneg g μ hμ
        (scalarEnergyDomainL2 g μ hμ k)).mono Set.Icc_subset_Ici_self
  have hcontL : ContinuousOn (fun t => scalarHeatFamily g μ hμ t
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))) (Set.Icc 0 T) :=
    (scalarHeatFamily_continuousOn_nonneg g μ hμ
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))).mono Set.Icc_subset_Ici_self
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hcont
    (fun s hs => scalarHeat_compact_hasDerivAt g hK μ hμ k hs.1)
    (ContinuousOn.intervalIntegrable_of_Icc hT.le hcontL)
  simpa only [scalarHeatFamily_zero, one_apply_eq_self] using hFTC

/-- The compact scalar difference quotient tends to its actual project
Laplacian in the original scalar L² space. -/
theorem scalarHeat_compact_generator_limit (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) :
    Tendsto (fun t : ℝ => t⁻¹ •
      (scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ k) - scalarEnergyDomainL2 g μ hμ k))
      (𝓝[>] 0) (𝓝 (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))) := by
  have hc := scalarHeatFamily_continuousOn_nonneg g μ hμ
    (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))
  have hcont0 : ContinuousWithinAt (fun t => scalarHeatFamily g μ hμ t
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))) (Set.Ici 0) 0 :=
    hc 0 Set.self_mem_Ici
  have hder := intervalIntegral.integral_hasDerivWithinAt_right
    (a := (0 : ℝ)) (b := (0 : ℝ)) (s := Set.Ici (0 : ℝ)) (t := Set.Ioi (0 : ℝ))
    (f := fun s => scalarHeatFamily g μ hμ s
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k)))
    (by simp : IntervalIntegrable (fun s => scalarHeatFamily g μ hμ s
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))) volume 0 0)
    ((hc.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
    (hcont0.mono Set.Ioi_subset_Ici_self)
  have hset : Set.Ici (0 : ℝ) \ {(0 : ℝ)} = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hx, hx0⟩
      exact lt_of_le_of_ne hx (Ne.symm hx0)
    · intro hx
      exact ⟨hx.le, hx.ne'⟩
  have hlim := hasDerivWithinAt_iff_tendsto_slope.mp hder
  rw [hset] at hlim
  simp only [scalarHeatFamily_zero, one_apply_eq_self] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [slope_def_module, sub_zero, intervalIntegral.integral_same, sub_zero,
    scalarHeat_compact_duhamel g hK μ hμ k ht]

end Yau.LeafProofs.L19Aux
