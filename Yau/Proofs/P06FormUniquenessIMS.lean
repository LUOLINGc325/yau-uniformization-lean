import Yau.Proofs.P06FormUniquenessInitial

/-! Compact localization of the genuine Hodge IMS identity. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem hodgeRealForm_eq_at_of_eventuallyEq
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A B : RealForm M k}
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (y : M.Carrier)
    (hAB : ∀ᶠ x in 𝓝 y, A x = B x) :
    L03.hodgeRealForm g.form k A y = L03.hodgeRealForm g.form k B y := by
  apply sub_eq_zero.mp
  apply (L03.formComponents_center_eq_zero_iff
    (L03.hodgeRealForm g.form k A - L03.hodgeRealForm g.form k B) y).mp
  funext I
  change formComponents (L03.hodgeRealForm g.form k A) y (chartPt y y) I -
    formComponents (L03.hodgeRealForm g.form k B) y (chartPt y y) I = 0
  have hz : chartPt y y ∈ chartTarget y := mem_extChartAt_target y
  rw [L03.hodgeRealForm_represents g μ hμ A hA y _ hz I,
    L03.hodgeRealForm_represents g μ hμ B hB y _ hz I]
  apply sub_eq_zero.mpr
  apply congrFun (L03.hodgeComponents_congr_nhds g.form y ?_) I
  apply L03.formComponents_eventuallyEq_of_eventuallyEq y hz
  have hi : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  simpa only [hi] using hAB

/-- The exact compact-cutoff IMS identity holds for every smooth form.
Only the scalar cutoff has compact support. -/
theorem integral_hodge_cutoff_IMS_local
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (A : RealForm M k) (hA : SmoothRealForm A) :
    (∫ y, L03.hodgeEnergyDensity g.form k
      (L03.multiplyRealForm η A) (L03.multiplyRealForm η A) y ∂μ) =
    (∫ y, η y ^ 2 * formInner g.form (L03.hodgeRealForm g.form k A) A y ∂μ) +
      ∫ y, L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y ∂μ := by
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  obtain ⟨K, hK, hηK⟩ := exists_compact_superset hcη.isCompact
  obtain ⟨ζ, hζ, hcζ, hζK⟩ := L03.exists_smooth_compact_scalar_one_on hK
  let B := L03.multiplyRealForm ζ A
  have hB : SmoothRealForm B := L03.smoothRealForm_multiply ζ A hζ hA
  have hcB : CompactlySupportedRealForm B :=
    L03.compactlySupportedRealForm_multiply_scalar ζ hcζ A
  have hBA (y : M.Carrier) (hy : y ∈ tsupport η) : B y = A y := by
    change ζ y • A y = A y
    rw [hζK y (interior_subset (hηK hy)), one_smul]
  have hHBA (y : M.Carrier) (hy : y ∈ tsupport η) :
      L03.hodgeRealForm g.form k B y = L03.hodgeRealForm g.form k A y := by
    apply hodgeRealForm_eq_at_of_eventuallyEq g μ hμ hB hA y
    filter_upwards [isOpen_interior.mem_nhds (hηK hy)] with x hx
    change ζ x • A x = A x
    rw [hζK x (interior_subset hx), one_smul]
  have hηBA : L03.multiplyRealForm η B = L03.multiplyRealForm η A := by
    funext y
    by_cases hy : y ∈ tsupport η
    · exact congrArg (η y • ·) (hBA y hy)
    · simp only [L03.multiplyRealForm, image_eq_zero_of_notMem_tsupport hy, zero_smul]
  have hmain : (fun y => formInner g.form (L03.hodgeRealForm g.form k B)
      (L03.multiplyRealForm (fun y => η y * η y) B) y) =
      fun y => η y ^ 2 * formInner g.form (L03.hodgeRealForm g.form k A) A y := by
    funext y
    rw [L03.multiplyRealForm_inner_right]
    by_cases hy : y ∈ tsupport η
    · rw [L03.formInner_congr_at g.form (hHBA y hy) (hBA y hy), pow_two]
    · simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero, zero_mul, zero_pow (by omega : 2 ≠ 0)]
  have herr : (fun y => L18Aux.scalarGradientPair g.form η η y * formNormSq g.form B y) =
      fun y => L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y := by
    funext y
    by_cases hy : y ∈ tsupport η
    · rw [L03.formNormSq_congr_at g.form (hBA y hy)]
    · simp only [L18Aux.scalarGradientPair_zero_of_notMem_tsupport g.form η η hy, zero_mul]
  have hh := L03.integral_hodge_cutoff_IMS g μ hμ η hη B hB hcB
  rwa [hηBA, hmain, herr] at hh

/-- Positivity of the original d/δ quadratic form gives the local
generator energy inequality without any curvature lower bound. -/
theorem integral_hodge_cutoff_generator_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (A : RealForm M k) (hA : SmoothRealForm A) :
    -(∫ y, η y ^ 2 * formInner g.form (L03.hodgeRealForm g.form k A) A y ∂μ) ≤
      ∫ y, L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y ∂μ := by
  have hh := integral_hodge_cutoff_IMS_local g μ hμ η hη hcη A hA
  have hn : 0 ≤ (∫ y, L03.hodgeEnergyDensity g.form k
      (L03.multiplyRealForm η A) (L03.multiplyRealForm η A) y ∂μ) :=
    integral_nonneg (fun y => L03.hodgeEnergyDensity_self_nonneg g.form
      (L03.multiplyRealForm η A) y)
  linarith

end Yau.NodeProofs.P06Aux
