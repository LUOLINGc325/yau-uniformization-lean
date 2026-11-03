import Yau.LeafProofs.L03HodgeWeakEnergy

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem exists_smooth_compact_scalar_one_on {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ ζ : M.Carrier → ℝ, SmoothFn ζ ∧ HasCompactSupport ζ ∧ ∀ y ∈ K, ζ y = 1 := by
  classical
  obtain ⟨s, φ, hφ, hsum⟩ := exists_finite_compact_smooth_chart_partition hK
  let ψ := fun i : s => L18Aux.chartPushforwardZero (i : M.Carrier) (φ i)
  have hs (i : s) : SmoothFn (ψ i) := L18Aux.smoothFn_chartPushforwardZero _ (hφ i).1 (hφ i).2.1 (hφ i).2.2
  have hc (i : s) : HasCompactSupport (ψ i) :=
    (L18Aux.chartPushforwardZero_properties _ (hφ i).1 (hφ i).2.1 (hφ i).2.2).1
  let L : Set M.Carrier := ⋃ i : s, tsupport (ψ i)
  have hL : IsCompact L := isCompact_iUnion hc
  refine ⟨fun y => ∑ i : s, ψ i y, L18Aux.smoothFn_sum ψ hs, ?_, hsum⟩
  apply hL.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hL.isClosed
  intro y hy
  by_contra hn
  have hz (i : s) : ψ i y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hn (Set.mem_iUnion.mpr ⟨i, h⟩))
  exact hy (by simp only [hz, Finset.sum_const_zero])

/-- The original raw negative Hodge deficiency equation has the exact
constant-one cutoff energy bound. Local first derivatives are supplied
by actual regularization; no H¹ hypothesis on the raw section is used. -/
theorem hodge_deficiency_cutoff_energy_le
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    (∫ y, formNormSq g.form (multiplyRealForm η A) y ∂μ) ≤
      ∫ y, L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y ∂μ := by
  classical
  obtain ⟨ζ, hζ, hcζ, hζK⟩ := exists_smooth_compact_scalar_one_on hcη
  let T := multiplyRealForm ζ A
  have hT : L2RealForm g.form μ T := l2RealForm_multiply_smooth_compact g μ ζ hζ hcζ A hmax.1
  obtain ⟨L, hL, As, V, W, hAsall, hV, hW, htT, htV, htW⟩ :=
    exists_hodge_compact_multiplier_energy_approximation g μ hμ A hmax ζ hζ hcζ
  have hAs (m : ℕ) := (hAsall m).1
  have hcAs (m : ℕ) := (hAsall m).2.1
  have hA2 (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _ (hAs m) (hcAs m)
  have hdA (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _
    (exteriorRealForm_smooth _ (hAs m)) (exteriorRealForm_compactlySupported _ (hAs m) (hcAs m))
  have hlA (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _
    (hodgeLowerRealForm_smooth_compact g μ hμ _ (hAs m) (hcAs m)).1
    (hodgeLowerRealForm_smooth_compact g μ hμ _ (hAs m) (hcAs m)).2
  let η2 := fun y => η y * η y
  have hsη2 : SmoothFn η2 := fun x => (hη x).mul (hη x)
  have hcη2 : HasCompactSupport η2 := hcη.mul_right
  let Bs := fun m => multiplyRealForm η2 (As m)
  have hsB (m : ℕ) := smoothRealForm_multiply η2 _ hsη2 (hAs m)
  have hcB (m : ℕ) := compactlySupportedRealForm_multiply η2 _ (hcAs m)
  have hB2 (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _ (hsB m) (hcB m)
  have hdB (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _
    (exteriorRealForm_smooth _ (hsB m)) (exteriorRealForm_compactlySupported _ (hsB m) (hcB m))
  have hlB (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _
    (hodgeLowerRealForm_smooth_compact g μ hμ _ (hsB m) (hcB m)).1
    (hodgeLowerRealForm_smooth_compact g μ hμ _ (hsB m) (hcB m)).2
  let va := realizeActualForm g μ V hV
  let wa := realizeActualForm g μ W hW
  let ds := fun m => realizeActualForm g μ (exteriorRealForm (As m)) (hdA m)
  let ls := fun m => realizeActualForm g μ (hodgeLowerRealForm g.form k (As m)) (hlA m)
  let db := fun m => realizeActualForm g μ (exteriorRealForm (Bs m)) (hdB m)
  let lb := fun m => realizeActualForm g μ (hodgeLowerRealForm g.form k (Bs m)) (hlB m)
  have hds : Tendsto ds atTop (𝓝 va) := (tendsto_realizeL2Form_iff g μ _ _).mpr htV
  have hls : Tendsto ls atTop (𝓝 wa) := (tendsto_realizeL2Form_iff g μ _ _).mpr htW
  obtain ⟨P, Q, hdb, hlb⟩ := exists_hodge_energy_cutoff_limits g μ hμ As hAs hcAs T V W hT hV hW
    htT htV htW η2 hsη2 hcη2
  have hdb' : Tendsto db atTop (𝓝 P) := hdb
  have hlb' : Tendsto lb atTop (𝓝 Q) := hlb
  let E := inner ℝ va P + inner ℝ wa Q
  have hfixed : Tendsto (fun m => inner ℝ va (db m) + inner ℝ wa (lb m)) atTop (𝓝 E) :=
    (tendsto_const_nhds.inner hdb').add (tendsto_const_nhds.inner hlb')
  have hBpair (m : ℕ) : inner ℝ va (db m) + inner ℝ wa (lb m) =
      -(∫ y, formInner g.form A (Bs m) y ∂μ) := by
    have he := hodge_energy_limit_pairing g μ hμ As hAs hcAs T V W hT hV hW htT htV htW
      (Bs m) (hsB m) (hcB m)
    have hb := hodge_deficiency_buffer_pairing g μ hμ A hmax ζ (Bs m) (hsB m) (hcB m)
      (fun y hy => hζK y (((multiplyRealForm_support_subset_scalar η2 (As m)).trans
        (tsupport_mul_subset_left (f := η) (g := η))) hy))
    simpa only [va, wa, db, lb, realizeActualForm, realizeL2Form_inner, L2FormSpace.toSection_ofSection]
      using he.trans hb
  have hη2T : L2RealForm g.form μ (multiplyRealForm η2 T) :=
    l2RealForm_multiply_smooth_compact g μ η2 hsη2 hcη2 T hT
  have hBt := formL2DistanceSq_multiply_compact_tendsto g μ As T hA2 hT htT η2 hsη2 hcη2
  have hR := (formL2DistanceSq_tendsto_integral_pairing g μ Bs (multiplyRealForm η2 T) A
    hB2 hη2T hmax.1 hBt).neg
  have hEq : E = -(∫ y, formInner g.form A (multiplyRealForm η2 T) y ∂μ) := by
    apply tendsto_nhds_unique hfixed
    have hR' : Tendsto (fun m => -(∫ y, formInner g.form A (Bs m) y ∂μ)) atTop
        (𝓝 (-(∫ y, formInner g.form A (multiplyRealForm η2 T) y ∂μ))) := by
      simpa only [formInner_symm g.form A] using hR
    exact hR'.congr' (Eventually.of_forall fun m => (hBpair m).symm)
  have hdiag : Tendsto (fun m => inner ℝ (ds m) (db m) + inner ℝ (ls m) (lb m)) atTop (𝓝 E) :=
    (hds.inner hdb').add (hls.inner hlb')
  let w := L18Aux.scalarGradientPair g.form η η
  have hsw : SmoothFn w := L18Aux.smoothFn_scalarGradientPair g hη hη
  have hcw : HasCompactSupport w := L18Aux.scalarGradientPair_hasCompactSupport g.form η η hcη
  obtain ⟨C, hC⟩ := (L18Aux.continuous_of_smoothFn hsw).bounded_above_of_compact_support hcw
  have hwt := integral_weighted_formNormSq_tendsto g μ As T hA2 hT htT w
    (L18Aux.continuous_of_smoothFn hsw).aestronglyMeasurable (max C 0) (le_max_right _ _)
    (fun y => (show |w y| ≤ C by simpa only [Real.norm_eq_abs] using hC y).trans (le_max_left _ _))
  have hnonneg (m : ℕ) : 0 ≤ (inner ℝ (ds m) (db m) + inner ℝ (ls m) (lb m)) +
      ∫ y, w y * formNormSq g.form (As m) y ∂μ := by
    rw [← integral_hodgeEnergyDensity_realized g μ hμ _ _ (hAs m) (hsB m) (hcAs m) (hcB m)]
    rw [integral_hodgeEnergyDensity g μ hμ _ _ (hAs m) (hsB m) (hcAs m) (hcB m),
      ← integral_hodge_cutoff_IMS g μ hμ η hη (As m) (hAs m) (hcAs m)]
    exact integral_nonneg (hodgeEnergyDensity_self_nonneg g.form _)
  have hn := ge_of_tendsto' (hdiag.add hwt) hnonneg
  have hmul : multiplyRealForm η2 T = multiplyRealForm η2 A := by
    funext y
    by_cases hy : η y = 0
    · simp only [multiplyRealForm, η2, hy, mul_zero, zero_smul]
    · simp only [T, multiplyRealForm, hζK y (subset_tsupport η hy), one_smul]
  have hnorm : (fun y => formInner g.form A (multiplyRealForm η2 T) y) =
      formNormSq g.form (multiplyRealForm η A) := by
    rw [hmul]
    funext y
    rw [multiplyRealForm_inner_right, multiplyRealForm_normSq]
    change (η y * η y) * formNormSq g.form A y = η y ^ 2 * formNormSq g.form A y
    ring
  have hwT : (fun y => w y * formNormSq g.form T y) = fun y => w y * formNormSq g.form A y := by
    funext y
    by_cases hy : y ∈ tsupport η
    · simp only [T, multiplyRealForm_normSq, hζK y hy, one_pow, one_mul]
    · simp only [w, L18Aux.scalarGradientPair_zero_of_notMem_tsupport g.form η η hy, zero_mul]
  rw [hEq, hnorm, hwT] at hn
  linarith

end Yau.LeafProofs.L03
