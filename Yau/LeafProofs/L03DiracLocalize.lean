import Yau.LeafProofs.L03RawChartGraded

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- A finite smooth partition on a compact set can be represented by actual
compact model cutoffs, each supported in its genuine chart. -/
theorem exists_finite_compact_smooth_chart_partition {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ s : Finset M.Carrier, ∃ φ : s → ComplexVector n → ℝ,
      (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧
        tsupport (φ i) ⊆ chartTarget (i : M.Carrier)) ∧
      ∀ y ∈ K, ∑ i : s, L18Aux.chartPushforwardZero (i : M.Carrier) (φ i) y = 1 := by
  classical
  obtain ⟨s, p, hp, _, hps, hsum⟩ := L18Aux.exists_finite_smooth_partition hK
  have hlocal (i : s) : ∃ φ : ComplexVector n → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ chartTarget (i : M.Carrier) ∧
      ∀ y ∈ K, L18Aux.chartPushforwardZero (i : M.Carrier) φ y = p i y := by
    let x : M.Carrier := i
    let Ki := K ∩ tsupport (p i)
    have hcKi : IsCompact Ki := hK.inter_right (isClosed_tsupport (p i))
    have hKiS : Ki ⊆ (extChartAt (ComplexModel n) x).source := fun _ hy => hps i hy.2
    let L := chartPt x '' Ki
    have hcL : IsCompact L := hcKi.image_of_continuousOn
      ((continuousOn_extChartAt (I := ComplexModel n) x).mono hKiS)
    have hLO : L ⊆ chartTarget x := by
      rintro z ⟨y, hy, rfl⟩
      exact (extChartAt (ComplexModel n) x).map_source (hKiS hy)
    obtain ⟨χ, hχ, hcχ, hχO, _, hχL⟩ :=
      exists_model_chart_cutoff (isOpen_extChartAt_target (I := ComplexModel n) x) hcL hLO
    let φ := fun z => χ z * p i (chartInv x z)
    have hφ := scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
      χ hχ hcχ hχO (fun z => p i (chartInv x z)) (hp i x)
    refine ⟨φ, hφ.1, hφ.2.1, hφ.2.2.trans hχO, ?_⟩
    intro y hyK
    by_cases hy : y ∈ (extChartAt (ComplexModel n) (i : M.Carrier)).source
    · have hi : chartInv (i : M.Carrier) (chartPt (i : M.Carrier) y) = y :=
        (extChartAt (ComplexModel n) (i : M.Carrier)).left_inv hy
      simp only [L18Aux.chartPushforwardZero, if_pos hy, φ, x, hi]
      by_cases hpy : p i y = 0
      · rw [hpy, mul_zero]
      · have hzL : chartPt (i : M.Carrier) y ∈ L := ⟨y, ⟨hyK, subset_tsupport (p i) hpy⟩, rfl⟩
        rw [(hχL _ hzL).1, one_mul]
    · have hpy : p i y = 0 := by
        by_contra hneq
        exact hy (hps i (subset_tsupport (p i) hneq))
      simp only [L18Aux.chartPushforwardZero, if_neg hy, hpy]
  choose φ hφ hcφ hsφ heq using hlocal
  refine ⟨s, φ, (fun i => ⟨hφ i, hcφ i, hsφ i⟩), ?_⟩
  intro y hy
  calc
    _ = ∑ i : s, p i y := Finset.sum_congr rfl (fun i _ => heq i y hy)
    _ = 1 := hsum y hy

/-- The exact formal-adjoint scalar row obeys the product rule used for
localization of the original rough maximal equation. -/
theorem diracFormalAdjointTestRow_mul {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r c : α)
    (φ ψ : ComplexVector n → ℝ) (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ)
    (z : ComplexVector n) :
    diracFormalAdjointTestRow g x b r c (fun y => φ y * ψ y) z =
      φ z * diracFormalAdjointTestRow g x b r c ψ z - ψ z *
        ∑ i : RIdx n, diracScalarDerivativeCoefficient g x b r c i z *
          fderiv ℝ φ z (realModelBasis n i) := by
  classical
  have hd (i : RIdx n) : fderiv ℝ (fun y => φ y * ψ y) z (realModelBasis n i) =
      φ z * fderiv ℝ ψ z (realModelBasis n i) + ψ z * fderiv ℝ φ z (realModelBasis n i) := by
    rw [fderiv_fun_mul (hφ z) (hψ z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [diracFormalAdjointTestRow, hd]
  let a := fun i => diracScalarDerivativeCoefficient g x b r c i z
  let da := fun i => fderiv ℝ (diracScalarDerivativeCoefficient g x b r c i) z (realModelBasis n i)
  have hs : (∑ i, (a i * (φ z * fderiv ℝ ψ z (realModelBasis n i) +
        ψ z * fderiv ℝ φ z (realModelBasis n i)) + da i * (φ z * ψ z))) =
      φ z * (∑ i, (a i * fderiv ℝ ψ z (realModelBasis n i) + da i * ψ z)) +
        ψ z * ∑ i, a i * fderiv ℝ φ z (realModelBasis n i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- Scalar chart multiplication commutes exactly with the raw graded zero
pullback, including off the chart target. -/
theorem modelGradedChartPullbackZero_chart_multiply (x : M.Carrier)
    (φ : ComplexVector n → ℝ) (A : OperatorCandidates.GradedRealForm M) :
    modelGradedChartPullbackZero
      (fun j => multiplyRealForm (L18Aux.chartPushforwardZero x φ) (A j)) x =
      fun z => φ z • modelGradedChartPullbackZero A x z := by
  funext z j
  by_cases hz : z ∈ chartTarget x
  · simp only [modelGradedChartPullbackZero, chartFormPullbackZero, if_pos hz, Pi.smul_apply]
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      multiplyRealForm, ContinuousAlternatingMap.smul_apply, L18Aux.chartPushforwardZero_chartInv x φ hz]
  · simp only [modelGradedChartPullbackZero, chartFormPullbackZero, if_neg hz, Pi.smul_apply, smul_zero]

/-- Every actual smooth compact chart multiplier of a global raw L²
section has ordinary global Euclidean L² zero-pullback coordinates. -/
theorem modelGradedChartPullbackZero_cutoff_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (x : M.Carrier)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    MemLp (fun z => φ z • modelGradedChartPullbackZero A x z) 2 (lebesgueC n) := by
  let η := L18Aux.chartPushforwardZero x φ
  have hηp := L18Aux.chartPushforwardZero_properties x hφ hcφ hφO
  have hη := L18Aux.smoothFn_chartPushforwardZero x hφ hcφ hφO
  have hηc := L18Aux.continuous_of_smoothFn hη
  obtain ⟨C, hC⟩ := hηc.bounded_above_of_compact_support hηp.1
  have hC0 : 0 ≤ C := (norm_nonneg (η x)).trans (hC x)
  let B := fun j => multiplyRealForm η (A j)
  have hB : OperatorCandidates.GradedL2 g.form μ B := by
    apply (gradedL2_iff g.form μ B).mpr
    intro j
    exact l2RealForm_multiply_bounded g μ η hηc.aestronglyMeasurable C hC0
      (fun y => by simpa only [← Real.norm_eq_abs] using hC y) (A j) (hA.2 j)
  have hcB (j : ℕ) : CompactlySupportedRealForm (B j) :=
    compactlySupportedRealForm_multiply_scalar η hηp.1 (A j)
  have hsB (j : ℕ) : closure {y | B j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source :=
    (multiplyRealForm_support_subset_scalar η (A j)).trans hηp.2.2
  have hm := (modelGradedChartPullbackZero_properties g μ hμ B hB hcB x hsB
    (Module.finBasis ℝ (modelGradedFiber n))).2.2.1
  have he : modelGradedChartPullbackZero B x =
      fun z => φ z • modelGradedChartPullbackZero A x z :=
    modelGradedChartPullbackZero_chart_multiply x φ A
  rw [he] at hm
  exact hm

/-- The precise localized scalar coordinates are L², without ever requiring
an unrestricted raw chart pullback to be globally L². -/
theorem modelGradedChartPullbackZero_cutoff_coord_memLp {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) (c : α) :
    MemLp (fun z => φ z * b.repr (modelGradedChartPullbackZero A x z) c) 2 (lebesgueC n) := by
  have h := (b.coord c).toContinuousLinearMap.comp_memLp'
    (modelGradedChartPullbackZero_cutoff_memLp g μ hμ A hA x φ hφ hcφ hφO)
  simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul] using h

end Yau.LeafProofs.L03
