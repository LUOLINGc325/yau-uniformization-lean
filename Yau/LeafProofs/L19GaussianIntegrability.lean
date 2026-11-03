import Yau.LeafProofs.L12Complete
import Yau.LeafProofs.L19Harnack
import Yau.LeafProofs.L19Differential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Global Gaussian integrability from the actual exponential map and
its genuine Jacobian bound, including the null cut image. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal ContDiff InnerProductSpace ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem realExponential_strictMinimizing_measure_transport (g : SmoothMetric M)
    (o : M.Carrier) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    letI := underlyingRealTangentNormedAddCommGroup g.form o
    letI := underlyingRealTangentInnerProductSpace g.form o
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
    μ = Measure.map (realExponentialMap g o)
      (((realTangentVolume g o).withDensity
        (fun v => ENNReal.ofReal (realExponentialVolumeDensity g o v))).restrict
        (realStrictMinimizingVectors g o)) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form o
  letI := underlyingRealTangentInnerProductSpace g.form o
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
  let D := realStrictMinimizingVectors g o
  let E := realExponentialMap g o
  let J := fun v => ENNReal.ofReal (realExponentialVolumeDensity g o v)
  have hD : MeasurableSet D := measurableSet_realStrictMinimizingVectors g o
  have hE : Measurable E := (realExponentialMap_contMDiff g o).continuous.measurable
  have hi : InjOn E D := realExponentialMap_injOn_strictMinimizingVectors g o
  have hcover : (E '' D)ᶜ ⊆ realExponentialMap g o '' realCutEndpointVectors g o := by
    intro y hy
    obtain ⟨v, hv, hnorm⟩ := exists_minimizing_realExponential g o y
    have hvmin : v ∈ realMinimizingVectors g o := by
      change inducedDistance g.form o (realExponentialMap g o v) = ‖v‖
      rw [hv, hnorm]
    have hn : v ∉ D := fun hvD => hy ⟨v, hvD, hv⟩
    exact ⟨v, ⟨hvmin, hn⟩, hv⟩
  have hnull : μ ((E '' D)ᶜ) = 0 :=
    measure_mono_null hcover (realExponentialMap_cutEndpointVectors_image_measure_zero g o μ hμ)
  have hae : ∀ᵐ y ∂μ, y ∈ E '' D := ae_iff.mpr hnull
  have hrestrict : μ.restrict (E '' D) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have htransport : μ.restrict (E '' D) = Measure.map E
      (((realTangentVolume g o).withDensity J).restrict D) := by
    apply Measure.ext
    intro A hA
    have hs : MeasurableSet (D ∩ E ⁻¹' A) := hD.inter (hE hA)
    have himage : E '' (D ∩ E ⁻¹' A) = A ∩ E '' D := by
      ext y
      simp only [mem_image, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨v, ⟨hvD, hvA⟩, rfl⟩
        exact ⟨hvA, v, hvD, rfl⟩
      · rintro ⟨hyA, v, hvD, rfl⟩
        exact ⟨v, ⟨hvD, hyA⟩, rfl⟩
    rw [Measure.restrict_apply hA, Measure.map_apply hE hA,
      Measure.restrict_apply (hE hA), inter_comm (E ⁻¹' A) D,
      withDensity_apply J hs, ← himage]
    exact realExponentialMap_image_volume g o μ hμ _ hs (hi.mono inter_subset_left)
  exact hrestrict.symm.trans htransport

theorem realExponentialVolumeDensity_le_one_strict (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef) (o : M.Carrier)
    {v : TangentSpace 𝓘(ℝ, ComplexVector n) o} (hv : v ∈ realStrictMinimizingVectors g o) :
    realExponentialVolumeDensity g o v ≤ 1 := by
  letI := underlyingRealTangentNormedAddCommGroup g.form o
  letI := underlyingRealTangentInnerProductSpace g.form o
  obtain ⟨q, hq⟩ := hv
  have hq1 : 1 < (q.val : ℝ) := by exact_mod_cast q.property
  have hqpos : 0 < (q.val : ℝ) := zero_lt_one.trans hq1
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨o, v⟩
  have hmin : inducedDistance g.form p.proj (realGeodesicFlow g p q.val).proj =
      (q.val : ℝ) * ‖p.2‖ := by
    change inducedDistance g.form o (realGeodesicFlow g ⟨o, v⟩ q.val).proj = _
    rw [← realExponentialMap_smul]
    change inducedDistance g.form o (realExponentialMap g o ((q.val : ℝ) • v)) = _ at hq ⊢
    rw [hq, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
  have hdet := realMinimizingJacobiPositive g p q.val hqpos hmin
  have hh := realExponentialVolumeDensity_le_one g hK hRic p q.val hdet ⟨zero_lt_one, hq1⟩
  simpa only [p, one_smul] using hh

theorem strictExponentialDensity_measure_le (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef) (o : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form o
    letI := underlyingRealTangentInnerProductSpace g.form o
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
    ((realTangentVolume g o).withDensity
      (fun v => ENNReal.ofReal (realExponentialVolumeDensity g o v))).restrict
        (realStrictMinimizingVectors g o) ≤ realTangentVolume g o := by
  letI := underlyingRealTangentNormedAddCommGroup g.form o
  letI := underlyingRealTangentInnerProductSpace g.form o
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
  apply Measure.le_iff.mpr
  intro A hA
  have hD := measurableSet_realStrictMinimizingVectors g o
  rw [Measure.restrict_apply hA, withDensity_apply _ (hA.inter hD)]
  calc
    _ ≤ ∫⁻ v in A ∩ realStrictMinimizingVectors g o, (1 : ℝ≥0∞) ∂realTangentVolume g o := by
      apply setLIntegral_mono' (hA.inter hD)
      intro v hv
      exact (ENNReal.ofReal_le_ofReal (realExponentialVolumeDensity_le_one_strict g hK hRic o hv.2)).trans_eq (by simp)
    _ = (realTangentVolume g o) (A ∩ realStrictMinimizingVectors g o) := by simp
    _ ≤ (realTangentVolume g o) A := measure_mono inter_subset_left

theorem integrable_tangent_gaussian (g : SmoothMetric M) (o : M.Carrier) {a : ℝ} (ha : 0 < a) :
    letI := underlyingRealTangentNormedAddCommGroup g.form o
    letI := underlyingRealTangentInnerProductSpace g.form o
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
    Integrable (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) o => Real.exp (-a * ‖v‖ ^ 2))
      (realTangentVolume g o) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form o
  letI := underlyingRealTangentInnerProductSpace g.form o
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
  rw [realTangentVolume, OrthonormalBasis.addHaar_eq_volume]
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := TangentSpace 𝓘(ℝ, ComplexVector n) o)
    (b := (a : ℂ)) (by simpa using ha) (0 : ℂ) 0
  have hr := h.re
  convert hr using 1
  funext v
  simp [← Complex.ofReal_pow, Complex.exp_re]

theorem integrable_exp_neg_distance_sq (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a : ℝ} (ha : 0 < a) :
    Integrable (fun y => Real.exp (-a * inducedDistance g.form o y ^ 2)) μ := by
  letI := underlyingRealTangentNormedAddCommGroup g.form o
  letI := underlyingRealTangentInnerProductSpace g.form o
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
  let D := realStrictMinimizingVectors g o
  let E := realExponentialMap g o
  let J := fun v => ENNReal.ofReal (realExponentialVolumeDensity g o v)
  let ν := ((realTangentVolume g o).withDensity J).restrict D
  have hφ : Continuous (fun y => Real.exp (-a * inducedDistance g.form o y ^ 2)) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_distFrom g o).pow 2))
  have hf : Measurable (fun y => ENNReal.ofReal (Real.exp (-a * inducedDistance g.form o y ^ 2))) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hbound : (∫⁻ y, ENNReal.ofReal (Real.exp (-a * inducedDistance g.form o y ^ 2)) ∂μ) ≤
      ∫⁻ v, ENNReal.ofReal (Real.exp (-a * ‖v‖ ^ 2)) ∂realTangentVolume g o := by
    have hmap := realExponential_strictMinimizing_measure_transport g o μ hμ
    rw [hmap, lintegral_map hf (realExponentialMap_contMDiff g o).continuous.measurable]
    change (∫⁻ v in D, ENNReal.ofReal (Real.exp (-a * inducedDistance g.form o (E v) ^ 2))
      ∂(realTangentVolume g o).withDensity J) ≤ _
    have heq : (∫⁻ v in D, ENNReal.ofReal (Real.exp (-a * inducedDistance g.form o (E v) ^ 2))
        ∂(realTangentVolume g o).withDensity J) =
        ∫⁻ v, ENNReal.ofReal (Real.exp (-a * ‖v‖ ^ 2)) ∂ν := by
      apply setLIntegral_congr_fun (measurableSet_realStrictMinimizingVectors g o)
      intro v hv
      have hmin := realStrictMinimizingVectors_subset g o hv
      change inducedDistance g.form o (realExponentialMap g o v) = ‖v‖ at hmin
      exact congrArg (fun r : ℝ => ENNReal.ofReal (Real.exp (-a * r ^ 2))) hmin
    rw [heq]
    exact lintegral_mono' (strictExponentialDensity_measure_le g hK hRic o) le_rfl
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => (Real.exp_pos _).le))).mpr
  exact lt_of_le_of_lt hbound ((hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) o => (Real.exp_pos (-a * ‖v‖ ^ 2)).le))).mp
      (integrable_tangent_gaussian g o ha).2)

theorem memLp_exp_neg_distance_sq (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a : ℝ} (ha : 0 < a) :
    MemLp (fun y => Real.exp (-a * inducedDistance g.form o y ^ 2)) 2 μ := by
  have hφ : Continuous (fun y => Real.exp (-a * inducedDistance g.form o y ^ 2)) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_distFrom g o).pow 2))
  apply (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mpr
  have hi := integrable_exp_neg_distance_sq g hK hRic μ hμ o (a := 2 * a) (by positivity)
  convert hi using 1
  funext y
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Arbitrary original positive heat solutions have finite Gaussian
weighted mass at every positive time.  Their required growth control
is derived from the proved original Harnack inequality. -/
theorem positiveHeatSolution_gaussian_weight_integrable (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : M.Carrier → ℝ → ℝ}
    (hu : LeafCandidates.PositiveHeatSolution g.form u) (o : M.Carrier)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    Integrable (fun x => u x t * Real.exp (-a * inducedDistance g.form o x ^ 2)) μ := by
  obtain ⟨C, hC, hbound⟩ := positiveHeatSolution_gaussian_growth liYauDifferential g
    hcomplete hK hRic hu o ht ha
  have hi := (integrable_exp_neg_distance_sq g hK hRic μ hμ o
    (a := a / 2) (by positivity)).const_mul (C / t ^ n)
  have hcontu := continuous_of_smoothFn (positiveHeatSolution_slice g.form hu ht)
  have hφ : Continuous (fun x => Real.exp (-a * inducedDistance g.form o x ^ 2)) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_distFrom g o).pow 2))
  apply hi.mono' (hcontu.mul hφ).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖u x t * Real.exp (-a * inducedDistance g.form o x ^ 2)‖ ≤
    C / t ^ n * Real.exp (-(a / 2) * inducedDistance g.form o x ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hu.2 x t ht).1.le (Real.exp_pos _).le)]
  calc
    _ ≤ (C / t ^ n * Real.exp ((a / 2) * inducedDistance g.form o x ^ 2)) *
        Real.exp (-a * inducedDistance g.form o x ^ 2) :=
      mul_le_mul_of_nonneg_right (hbound t ht le_rfl x) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end Yau.LeafProofs.L19Aux
