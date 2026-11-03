import Yau.LeafProofs.L23FieldMetricNormalRadius

/-! The genuine unit geodesic has length equal to its physical initial speed. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem chartGeodesic_unit_pathELength
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ u ∈ Set.Ioo (-ε) (1+ε), (η u).1 ∈ chartTarget c ∧
      HasDerivAt η (chartGeodesicSpray h c (η u)) u) :
    fieldPathELength h (fun u => chartInv c (η u).1) 0 1 =
      ENNReal.ofReal (chartVectorNorm h c (η 0).1 (η 0).2) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hnorm (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ‖realCurveVelocity (fun s => chartInv c (η s).1) u‖ = chartVectorNorm h c (η 0).1 (η 0).2 := by
    have hu' : u ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith [hu.1,hu.2]
    have H := chartGeodesicEnergy_eq_actual_speed_sq h hh c η (hs u hu').1 (hs u hu').2
    have HE := chartGeodesicEnergy_constant h hh c η hs hu' h₀
    change _ = Real.sqrt (chartGeodesicEnergy h c (η 0))
    rw [← HE,H,Real.sqrt_sq (norm_nonneg _)]
  change Manifold.pathELength 𝓘(ℝ, ComplexVector n) (fun u => chartInv c (η u).1) 0 1 = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hEq : (fun u => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n)
      (fun s => chartInv c (η s).1) u 1‖ₑ) =ᵐ[
        volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun _ => ENNReal.ofReal (chartVectorNorm h c (η 0).1 (η 0).2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [← ofReal_norm]
    exact congrArg ENNReal.ofReal (hnorm u hu)
  rw [lintegral_congr_ae hEq]
  simp

theorem inducedDistance_chartGeodesic_unit_le
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ u ∈ Set.Ioo (-ε) (1+ε), (η u).1 ∈ chartTarget c ∧
      HasDerivAt η (chartGeodesicSpray h c (η u)) u) :
    inducedDistance h (chartInv c (η 0).1) (chartInv c (η 1).1) ≤
      chartVectorNorm h c (η 0).1 (η 0).2 := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  have hC := chartGeodesic_curve_contMDiffOn_Icc h hh c η
    (fun u (hu : u ∈ Set.Icc (0 : ℝ) 1) => hs u (by constructor <;> linarith [hu.1,hu.2]))
  have HD := Manifold.riemannianEDist_le_pathELength (hC.of_le (by simp)) rfl rfl zero_le_one
  rw [← inducedDistance_eq_riemannianEDist h hh,
    ← fieldPathELength,chartGeodesic_unit_pathELength h hh c η hε hs] at HD
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp HD

end Yau.LeafProofs.L23Aux
