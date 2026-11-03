import Yau.LeafProofs.L23LocalDistanceSupportPolygonLower

/-! Actual project curve lengths on subintervals and their cumulative primitive. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem fieldPathELength_eq_curveSpeed_integral
    (h : HermitianField M) {q y : M.Carrier} (γ : IntegrableCurve h q y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    fieldPathELength h γ.1 a b = ENNReal.ofReal (∫ u in Set.Icc a b, curveSpeed h γ.1 u) := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  have hi := γ.2.mono_set (Set.Icc_subset_Icc ha hb)
  rw [fieldPathELength,Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => Real.sqrt_nonneg _)]
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply lintegral_congr_ae
  have hbreak : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ γ.1.breakpoints :=
    γ.1.breakpoints.finite_toSet.countable.ae_notMem volume
  filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hbreak] with u hu hbu
  rw [← ofReal_norm]
  exact congrArg ENNReal.ofReal (realCurveVelocity_norm h γ.1 ⟨ha.trans_lt hu.1,hu.2.trans_le hb⟩ hbu)

theorem inducedDistance_curve_segment_le_integral
    (h : HermitianField M) (hh : MetricSmooth h) {q y : M.Carrier} (γ : IntegrableCurve h q y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    inducedDistance h (γ.1 a) (γ.1 b) ≤ ∫ u in Set.Icc a b, curveSpeed h γ.1 u := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  have HD := riemannianEDist_le_pathELength_of_finite_exceptions h hh γ.1.breakpoints hab
    (γ.1.continuous_on.mono (Set.Icc_subset_Icc ha hb)) (fun u hu hnot => ?_)
  · rw [← inducedDistance_eq_riemannianEDist h hh,
      ← fieldPathELength,fieldPathELength_eq_curveSpeed_integral h γ ha hab hb] at HD
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => Real.sqrt_nonneg _)).mp HD
  · rw [contMDiffAt_iff]
    refine ⟨γ.1.continuous_on.continuousAt (Icc_mem_nhds (ha.trans_lt hu.1) (hu.2.trans_le hb)),?_⟩
    simp only [real_extChartAt_eq,mfld_simps,contDiffWithinAt_univ]
    convert! γ.1.piecewise_c1 u hnot using 1

theorem continuousOn_curveLengthPrimitive
    (h : HermitianField M) {q y : M.Carrier} (γ : IntegrableCurve h q y) :
    ContinuousOn (fun t => ∫ u in (0 : ℝ)..t, curveSpeed h γ.1 u) (Set.Icc (0 : ℝ) 1) := by
  have H : IntegrableOn (curveSpeed h γ.1) (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le zero_le_one] using γ.2
  simpa only [Set.uIcc_of_le zero_le_one] using intervalIntegral.continuousOn_primitive_interval H

end Yau.LeafProofs.L23Aux
