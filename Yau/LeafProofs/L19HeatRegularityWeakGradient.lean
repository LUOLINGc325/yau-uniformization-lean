import Yau.LeafProofs.L19HeatRegularityGradient

/-! Genuine spatial weak derivatives of the completed scalar energy space. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Spatial integration by parts for the actual core scalar in an actual
chart, with the genuine Euclidean test support. -/
theorem scalarEnergy_core_chart_ibp (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOt : O ⊆ chartTarget x)
    (f : CompactScalar M) {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η)
    (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) (i : RIdx n) :
    (∫ z in O, inChart x f z * rDeriv η z i) =
      -(∫ z in O, rDeriv (inChart x f) z i * η z) := by
  have h₁ : (∫ z in O, inChart x f z * rDeriv η z i) =
      ∫ z, inChart x f z * rDeriv η z i := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hh : z ∉ tsupport (fun w => rDeriv η w i) :=
      fun h => hz ((tsupport_fderiv_apply_subset ℝ (realVec i)).trans hηO h)
    rw [image_eq_zero_of_notMem_tsupport hh, mul_zero]
  have h₂ : (∫ z in O, rDeriv (inChart x f) z i * η z) =
      ∫ z, rDeriv (inChart x f) z i * η z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hηO h)), mul_zero]
  rw [h₁, h₂]
  have hh := integral_compactTest_direction_on (volume : Measure (ComplexVector n))
    hO hη hcη hηO ((f.2.1 x).mono hOt |>.of_le (by simp)) (realVec i)
  have he₁ : (fun z => inChart x f z * rDeriv η z i) =
      (fun z => fderiv ℝ η z (realVec i) * inChart x f z) := by
    funext z
    simp only [rDeriv, mul_comm]
  have he₂ : (fun z => rDeriv (inChart x f) z i * η z) =
      (fun z => η z * fderiv ℝ (inChart x f) z (realVec i)) := by
    funext z
    simp only [rDeriv, mul_comm]
  rw [he₁, he₂]
  linarith only [hh]

/-- The chart derivatives constructed by completion are genuine weak
spatial derivatives of the actual L² inclusion, not free gradient data. -/
theorem scalarEnergy_chartWeakGradient (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (v : ScalarEnergySpace g μ hμ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η)
    (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) (i : RIdx n) :
    (∫ z in O, scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
        (scalarEnergyL2 g μ hμ v) z * rDeriv η z i) =
      -(∫ z in O, scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i v z * η z) := by
  let R := scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
  let J := scalarEnergyL2 g μ hμ
  let D := scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
  have hηL : MemLp η 2 (volume.restrict O) :=
    hη.continuous.memLp_of_hasCompactSupport hcη |>.mono_measure Measure.restrict_le_self
  have hηD : MemLp (fun z => rDeriv η z i) 2 (volume.restrict O) :=
    ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcη.fderiv_apply ℝ (realVec i)) |>.mono_measure Measure.restrict_le_self
  let q : Lp ℝ 2 (volume.restrict O) := hηL.toLp η
  let qD : Lp ℝ 2 (volume.restrict O) := hηD.toLp (fun z => rDeriv η z i)
  have hpair : ∀ w : ScalarEnergySpace g μ hμ, ⟪R (J w), qD⟫_ℝ = -⟪D w, q⟫_ℝ := by
    intro w
    refine UniformSpace.Completion.induction_on w
      (p := fun w : ScalarEnergySpace g μ hμ => ⟪R (J w), qD⟫_ℝ = -⟪D w, q⟫_ℝ) ?_ ?_
    · exact isClosed_eq ((R.continuous.comp J.continuous).inner continuous_const)
        (D.continuous.inner continuous_const).neg
    · intro f
      rw [L2.inner_def, L2.inner_def]
      have hL : (∫ z in O, inner ℝ (R (J (f : ScalarEnergySpace g μ hμ)) z) (qD z)) =
          ∫ z in O, inChart x f z * rDeriv η z i := by
        apply integral_congr_ae
        filter_upwards [scalarEnergy_chartRestrictionCLM_core g μ hμ x hO hOc hOt f,
          hηD.coeFn_toLp] with z hz hq
        rw [hz, hq]
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
      have hR : (∫ z in O, inner ℝ (D (f : ScalarEnergySpace g μ hμ) z) (q z)) =
          ∫ z in O, rDeriv (inChart x f) z i * η z := by
        apply integral_congr_ae
        filter_upwards [scalarEnergy_chartDerivativeCLM_coe g μ hμ x hO hOc hOt i f,
          hηL.coeFn_toLp] with z hz hq
        rw [hz, hq]
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
      rw [hL, hR]
      exact scalarEnergy_core_chart_ibp x hO (subset_closure.trans hOt) f hη hcη hηO i
  have hL : ⟪R (J v), qD⟫_ℝ = ∫ z in O, R (J v) z * rDeriv η z i := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hηD.coeFn_toLp] with z hz
    change inner ℝ (R (J v) z) (qD z) = _
    rw [hz]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  have hR : ⟪D v, q⟫_ℝ = ∫ z in O, D v z * η z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hηL.coeFn_toLp] with z hz
    change inner ℝ (D v z) (q z) = _
    rw [hz]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [← hL, ← hR]
  exact hpair v

end Yau.LeafProofs.L19Aux
