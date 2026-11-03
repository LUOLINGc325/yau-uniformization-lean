import Yau.LeafProofs.L03CutoffEnergyLimits

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeEnergyDensity_eq_d_lower (g : HermitianField M) (A B : RealForm M k) :
    hodgeEnergyDensity g k A B = formInner g (exteriorRealForm A) (exteriorRealForm B) +
      formInner g (hodgeLowerRealForm g k A) (hodgeLowerRealForm g k B) := by
  cases k with
  | zero => simp only [hodgeEnergyDensity, hodgeLowerRealForm, formInner_zero_left, add_zero]
  | succ j => exact add_comm _ _

theorem integral_hodgeEnergyDensity_right (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : CompactlySupportedRealForm A) (hcB : CompactlySupportedRealForm B) :
    (∫ y, hodgeEnergyDensity g.form k A B y ∂μ) =
      ∫ y, formInner g.form A (hodgeRealForm g.form k B) y ∂μ := by
  rw [integral_hodgeEnergyDensity g μ hμ A B hA hB hcA hcB]
  exact (hodgeRealForm_symmetric g μ hμ A B hA hB hcA hcB).trans
    (by rw [formInner_symm g.form (hodgeRealForm g.form k B) A])

theorem integral_hodgeEnergyDensity_realized (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : CompactlySupportedRealForm A) (hcB : CompactlySupportedRealForm B) :
    (∫ y, hodgeEnergyDensity g.form k A B y ∂μ) =
      inner ℝ (realizeActualForm g μ (exteriorRealForm A)
        (smooth_compactlySupported_l2RealForm g μ hμ _ (exteriorRealForm_smooth A hA)
          (exteriorRealForm_compactlySupported A hA hcA)))
        (realizeActualForm g μ (exteriorRealForm B)
          (smooth_compactlySupported_l2RealForm g μ hμ _ (exteriorRealForm_smooth B hB)
            (exteriorRealForm_compactlySupported B hB hcB))) +
      inner ℝ (realizeActualForm g μ (hodgeLowerRealForm g.form k A)
        (smooth_compactlySupported_l2RealForm g μ hμ _
          (hodgeLowerRealForm_smooth_compact g μ hμ A hA hcA).1
          (hodgeLowerRealForm_smooth_compact g μ hμ A hA hcA).2))
        (realizeActualForm g μ (hodgeLowerRealForm g.form k B)
          (smooth_compactlySupported_l2RealForm g μ hμ _
            (hodgeLowerRealForm_smooth_compact g μ hμ B hB hcB).1
            (hodgeLowerRealForm_smooth_compact g μ hμ B hB hcB).2)) := by
  have hdA := smooth_compactlySupported_l2RealForm g μ hμ _ (exteriorRealForm_smooth A hA)
    (exteriorRealForm_compactlySupported A hA hcA)
  have hdB := smooth_compactlySupported_l2RealForm g μ hμ _ (exteriorRealForm_smooth B hB)
    (exteriorRealForm_compactlySupported B hB hcB)
  have hlA := smooth_compactlySupported_l2RealForm g μ hμ _
    (hodgeLowerRealForm_smooth_compact g μ hμ A hA hcA).1
    (hodgeLowerRealForm_smooth_compact g μ hμ A hA hcA).2
  have hlB := smooth_compactlySupported_l2RealForm g μ hμ _
    (hodgeLowerRealForm_smooth_compact g μ hμ B hB hcB).1
    (hodgeLowerRealForm_smooth_compact g μ hμ B hB hcB).2
  simp only [realizeActualForm, realizeL2Form_inner, L2FormSpace.toSection_ofSection]
  rw [hodgeEnergyDensity_eq_d_lower]
  exact integral_add (formInner_integrable g μ _ _ hdA hdB) (formInner_integrable g μ _ _ hlA hlB)

/-- Actual energy-graph convergence identifies the weak second-order
pairing against every genuine compact smooth test. -/
theorem hodge_energy_limit_pairing
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (As : ℕ → RealForm M k) (hAs : ∀ m, SmoothRealForm (As m))
    (hcAs : ∀ m, CompactlySupportedRealForm (As m))
    (T : RealForm M k) (V : RealForm M (k + 1)) (W : RealForm M (k - 1))
    (hT : L2RealForm g.form μ T) (hV : L2RealForm g.form μ V) (hW : L2RealForm g.form μ W)
    (htT : Tendsto (fun m => formL2DistanceSq g.form μ (As m) T) atTop (𝓝 0))
    (htV : Tendsto (fun m => formL2DistanceSq g.form μ (exteriorRealForm (As m)) V) atTop (𝓝 0))
    (htW : Tendsto (fun m => formL2DistanceSq g.form μ (hodgeLowerRealForm g.form k (As m)) W) atTop (𝓝 0))
    (B : RealForm M k) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form V (exteriorRealForm B) y ∂μ) +
      (∫ y, formInner g.form W (hodgeLowerRealForm g.form k B) y ∂μ) =
      ∫ y, formInner g.form T (hodgeRealForm g.form k B) y ∂μ := by
  have hdA (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _
    (exteriorRealForm_smooth _ (hAs m)) (exteriorRealForm_compactlySupported _ (hAs m) (hcAs m))
  have hlA (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _
    (hodgeLowerRealForm_smooth_compact g μ hμ _ (hAs m) (hcAs m)).1
    (hodgeLowerRealForm_smooth_compact g μ hμ _ (hAs m) (hcAs m)).2
  have hdB := smooth_compactlySupported_l2RealForm g μ hμ _
    (exteriorRealForm_smooth B hB) (exteriorRealForm_compactlySupported B hB hcB)
  have hlB := smooth_compactlySupported_l2RealForm g μ hμ _
    (hodgeLowerRealForm_smooth_compact g μ hμ B hB hcB).1
    (hodgeLowerRealForm_smooth_compact g μ hμ B hB hcB).2
  have hzB := smooth_compactlySupported_l2RealForm g μ hμ _
    (hodgeRealForm_smooth g μ hμ B hB) (hodgeRealForm_compactlySupported g μ hμ B hB hcB)
  have hv := formL2DistanceSq_tendsto_integral_pairing g μ _ V _ hdA hV hdB htV
  have hw := formL2DistanceSq_tendsto_integral_pairing g μ _ W _ hlA hW hlB htW
  have ht := formL2DistanceSq_tendsto_integral_pairing g μ As T _
    (fun m => smooth_compactlySupported_l2RealForm g μ hμ _ (hAs m) (hcAs m)) hT hzB htT
  have heq (m : ℕ) :
      (∫ y, formInner g.form (exteriorRealForm (As m)) (exteriorRealForm B) y ∂μ) +
        (∫ y, formInner g.form (hodgeLowerRealForm g.form k (As m)) (hodgeLowerRealForm g.form k B) y ∂μ) =
      ∫ y, formInner g.form (As m) (hodgeRealForm g.form k B) y ∂μ := by
    rw [← integral_add (formInner_integrable g μ _ _ (hdA m) hdB)
      (formInner_integrable g μ _ _ (hlA m) hlB)]
    change (∫ y, (formInner g.form (exteriorRealForm (As m)) (exteriorRealForm B) +
      formInner g.form (hodgeLowerRealForm g.form k (As m)) (hodgeLowerRealForm g.form k B)) y ∂μ) = _
    rw [← hodgeEnergyDensity_eq_d_lower]
    exact integral_hodgeEnergyDensity_right g μ hμ _ B (hAs m) hB (hcAs m) hcB
  exact tendsto_nhds_unique ((hv.add hw).congr' (Eventually.of_forall heq)) ht

theorem hodge_deficiency_buffer_pairing
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (ζ : M.Carrier → ℝ) (B : RealForm M k) (hB : SmoothRealForm B)
    (hcB : CompactlySupportedRealForm B) (hζ : ∀ y ∈ closure {y | B y ≠ 0}, ζ y = 1) :
    (∫ y, formInner g.form (multiplyRealForm ζ A) (hodgeRealForm g.form k B) y ∂μ) =
      -(∫ y, formInner g.form A B y ∂μ) := by
  have hcore := (hodgeCorePair_iff_computed g μ hμ B (hodgeRealForm g.form k B)).mpr ⟨hB, hcB, rfl⟩
  have hh := (hmax.2.2 B _ hcore).2.2
  calc
    _ = ∫ y, formInner g.form A (hodgeRealForm g.form k B) y ∂μ := by
      apply integral_congr_ae (Eventually.of_forall ?_)
      intro y
      rw [multiplyRealForm_inner_left]
      by_cases hz : hodgeRealForm g.form k B y = 0
      · have hi : formInner g.form A (hodgeRealForm g.form k B) y = 0 :=
          (formInner_congr_at g.form rfl hz).trans (congrFun (formInner_zero_right g.form A) y)
        rw [hi, mul_zero]
      · rw [hζ y (hodgeRealForm_support_subset g μ hμ B hB (subset_closure hz)), one_mul]
    _ = ∫ y, formInner g.form (-A) B y ∂μ := hh
    _ = _ := by
      have he : (-A : RealForm M k) = (-1 : ℝ) • A := (neg_one_smul ℝ A).symm
      rw [he, formInner_smul_left]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul]
      ring

theorem formL2DistanceSq_multiply_compact_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (As : ℕ → RealForm M k) (A : RealForm M k)
    (hAs : ∀ m, L2RealForm g.form μ (As m)) (hA : L2RealForm g.form μ A)
    (ht : Tendsto (fun m => formL2DistanceSq g.form μ (As m) A) atTop (𝓝 0))
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    Tendsto (fun m => formL2DistanceSq g.form μ (multiplyRealForm η (As m)) (multiplyRealForm η A))
      atTop (𝓝 0) := by
  obtain ⟨C, D, hC, _, hηb, _⟩ := exists_compact_cutoff_uniform_bounds g η hη hcη
  have hm := (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable (μ := μ)
  let U := fun m => L2FormSpace.ofSection (As m) (hAs m)
  let V := L2FormSpace.ofSection A hA
  have htU := (tendsto_realizeL2Form_iff g μ U V).mpr ht
  have htM := ((multiplyL2FormHilbert (k := k) g μ η hm C hC hηb).continuous.tendsto
    (realizeL2Form g μ V)).comp htU
  apply (tendsto_realizeL2Form_iff g μ
    (fun m => multiplyL2FormLinear g μ η hm C hC hηb (U m))
      (multiplyL2FormLinear g μ η hm C hC hηb V)).mp
  simpa only [Function.comp_def, multiplyL2FormHilbert_realize] using htM

/-- Strong convergence preserves an actual integrated squared fibre
norm with any bounded measurable scalar weight. -/
theorem integral_weighted_formNormSq_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (As : ℕ → RealForm M k) (A : RealForm M k)
    (hAs : ∀ m, L2RealForm g.form μ (As m)) (hA : L2RealForm g.form μ A)
    (ht : Tendsto (fun m => formL2DistanceSq g.form μ (As m) A) atTop (𝓝 0))
    (w : M.Carrier → ℝ) (hwm : AEStronglyMeasurable w μ)
    (C : ℝ) (hC : 0 ≤ C) (hw : ∀ y, |w y| ≤ C) :
    Tendsto (fun m => ∫ y, w y * formNormSq g.form (As m) y ∂μ) atTop
      (𝓝 (∫ y, w y * formNormSq g.form A y ∂μ)) := by
  let U := fun m => L2FormSpace.ofSection (As m) (hAs m)
  let V := L2FormSpace.ofSection A hA
  let P := multiplyL2FormHilbert (k := k) g μ w hwm C hC hw
  have htU := (tendsto_realizeL2Form_iff g μ U V).mpr ht
  have htM := (P.continuous.tendsto (realizeL2Form g μ V)).comp htU
  have he (B : L2FormSpace g μ k) : inner ℝ (P (realizeL2Form g μ B)) (realizeL2Form g μ B) =
      ∫ y, w y * formNormSq g.form B.toSection y ∂μ := by
    rw [multiplyL2FormHilbert_realize, realizeL2Form_inner, multiplyL2FormLinear_toSection]
    simp only [multiplyRealForm_inner_left]
    rfl
  have hh : Tendsto (fun m => inner ℝ (P (realizeL2Form g μ (U m))) (realizeL2Form g μ (U m)))
      atTop (𝓝 (inner ℝ (P (realizeL2Form g μ V)) (realizeL2Form g μ V))) := htM.inner htU
  simpa only [he, U, V, L2FormSpace.toSection_ofSection] using hh

end Yau.LeafProofs.L03
