import Yau.LeafProofs.L03HodgeJets
import Yau.LeafProofs.L03RawChartForms

open MeasureTheory Filter Module
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Yau.LeafProofs.L03.HodgeDivergenceWeak

variable {n k : ℕ} {M : ComplexManifold n}

abbrev Fiber (n k : ℕ) := HodgeJets.Fiber n k

/-- The actual degree-k form Gram, including Riemannian volume density. -/
def gram {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (z : ComplexVector n) : Matrix α α ℝ :=
  LinearMap.BilinForm.toMatrix b
    (Real.sqrt (realMetricFn g x z).det • modelFormMetricBilin g x z k)

theorem gram_entry {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (z : ComplexVector n) (r c : α) :
    gram g x b z r c = Real.sqrt (realMetricFn g x z).det *
      modelFormInner (realMetricFn g x z)⁻¹ (b r) (b c) := by
  simp only [gram, LinearMap.BilinForm.toMatrix_apply, LinearMap.smul_apply,
    smul_eq_mul, modelFormMetricBilin_apply]

theorem gram_symm {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (z : ComplexVector n) (r c : α) : gram g x b z r c = gram g x b z c r := by
  simp only [gram_entry, modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) (b r) (b c)]

theorem gram_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (r c : α) :
    ContDiffOn ℝ ∞ (fun z => gram g.form x b z r c) (chartTarget x) := by
  simp only [gram_entry]
  apply (L18Aux.volumeDensity_contDiffOn g x).mul
  apply contDiffOn_const.mul
  exact tensorCoefficientPairing_contDiffOn (fun z => (realMetricFn g.form x z)⁻¹)
    (fun _ I => b r (fun t => realVec (I t))) (fun _ I => b c (fun t => realVec (I t)))
    (chartTarget x) (L18Aux.realMetricFn_inverse_contDiffOn g x)
    (fun _ => contDiffOn_const) (fun _ => contDiffOn_const)

theorem gram_pairing {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (z : ComplexVector n) (P Q : Fiber n k) :
    Real.sqrt (realMetricFn g x z).det * modelFormInner (realMetricFn g x z)⁻¹ P Q =
      dotProduct (b.repr P) ((gram g x b z).mulVec (b.repr Q)) := by
  simpa only [gram, LinearMap.smul_apply, smul_eq_mul, modelFormMetricBilin_apply] using
    LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b
      (Real.sqrt (realMetricFn g x z).det • modelFormMetricBilin g x z k) P Q

/-- Chart transport for raw actual L² pairings with a chart-supported second factor. -/
theorem integral_formInner_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B)
    (hBzero : ∀ y, y ∉ (extChartAt (ComplexModel n) x).source → B y = 0) :
    (∫ y, formInner g.form A B y ∂μ) =
      ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
        modelFormInner (realMetricFn g.form x z)⁻¹ (chartForm A x z) (chartForm B x z)
        ∂lebesgueC n := by
  have hzero (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) :
      formInner g.form A B y = 0 := by
    calc
      _ = formInner g.form A 0 y := formInner_congr_at g.form rfl (hBzero y hy)
      _ = 0 := congrFun (formInner_zero_right g.form A) y
  have hm := (formInner_integrable g μ A B hA hB).aestronglyMeasurable.mono_measure
    (Measure.restrict_le_self : μ.restrict (extChartAt (ComplexModel n) x).source ≤ μ)
  calc
    _ = ∫ y in (extChartAt (ComplexModel n) x).source, formInner g.form A B y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
        formInner g.form A B (chartInv x z) ∂lebesgueC n := by
      simpa only [smul_eq_mul] using L18Aux.integral_chart_volume_ae g μ hμ x hm
    _ = _ := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only
      rw [modelFormInner_chartForm g.form A B x hz]

/-- The exact actual chart differential expression; only smooth tests are differentiated. -/
def testOperator (g : HermitianField M) (x : M.Carrier)
    (G : ComplexVector n → Fiber n k) (z : ComplexVector n) : Fiber n k :=
  -(∑ i, ∑ j, (realMetricFn g x z)⁻¹ i j •
      fderiv ℝ (fun y => fderiv ℝ G y (realModelBasis n j)) z (realModelBasis n i)) +
    (∑ i, HodgeJets.E1 g x k i z (fderiv ℝ G z (realModelBasis n i))) +
    HodgeJets.E0 g x k z (G z)

/-- The original maximal equation implies the genuine weighted vector test equation. -/
theorem maximalGraph_chart_vector_test {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (G : ComplexVector n → Fiber n k) (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x) :
    (∫ z in chartTarget x, dotProduct (b.repr (chartForm A x z))
      ((gram g.form x b z).mulVec (b.repr (testOperator g.form x G z + G z))) ∂lebesgueC n) = 0 := by
  let T := chartFormPushforward x G
  let Z := hodgeRealForm g.form k T
  have hT : SmoothRealForm T := chartFormPushforward_smooth x G hG hcG hGO
  have hcT : CompactlySupportedRealForm T := chartFormPushforward_compactlySupported x G hG hcG hGO
  have hTs := chartFormPushforward_source_support x G hG hcG hGO
  have hT0 (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) : T y = 0 := by
    by_contra hn
    exact hy (hTs (subset_closure hn))
  have hZ0 (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) : Z y = 0 := by
    by_contra hn
    exact hy (hTs ((hodgeRealForm_support_subset g μ hμ T hT) (subset_closure hn)))
  have hcore := hodgeRealForm_corePair g μ hμ T hT hcT
  have h := (hmax.2.2 T Z hcore).2.2
  have hZi := formInner_integrable g μ A Z hmax.1 (hodgeRealForm_l2 g μ hμ T hT hcT)
  have hTi := formInner_integrable g μ A T hmax.1 (smooth_compactlySupported_l2RealForm g μ hμ T hT hcT)
  have hz : (∫ y, formInner g.form A (Z + T) y ∂μ) = 0 := by
    rw [formInner_add_right]
    simp only [Pi.add_apply]
    rw [integral_add hZi hTi]
    have hn : formInner g.form (-A) T = -formInner g.form A T := by
      funext y
      have hnA : (-1 : ℝ) • A = -A := by
        funext t
        exact neg_one_smul ℝ (A t)
      simpa only [hnA, Pi.smul_apply, smul_eq_mul, neg_one_mul, Pi.neg_apply] using
        congrFun (formInner_smul_left g.form (-1) A T) y
    simp only [hn, Pi.neg_apply, integral_neg] at h
    linarith
  rw [integral_formInner_chart g μ hμ x A (Z + T) hmax.1
    (l2RealForm_add g μ Z T (hodgeRealForm_l2 g μ hμ T hT hcT)
      (smooth_compactlySupported_l2RealForm g μ hμ T hT hcT))
    (fun y hy => by change Z y + T y = 0; rw [hZ0 y hy, hT0 y hy, add_zero])] at hz
  calc
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
        modelFormInner (realMetricFn g.form x z)⁻¹ (chartForm A x z) (chartForm (Z + T) x z)
        ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hzt
      dsimp only
      rw [← gram_pairing]
      congr 2
      change testOperator g.form x G z + G z = chartForm Z x z + chartForm T x z
      rw [chartFormPushforward_to_chart x G hzt]
      congr 1
      exact (HodgeJets.chart_hodge_pushforward_expansion g μ hμ x G hG hcG hGO hzt).symm
    _ = 0 := hz

/-- An actual compact scalar chart cutoff of a raw degree-k L² form is Euclidean L². -/
theorem chart_cutoff_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (x : M.Carrier) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x) :
    MemLp (fun z => φ z • chartFormPullbackZero x A z) 2 (lebesgueC n) := by
  let η := L18Aux.chartPushforwardZero x φ
  have hηp := L18Aux.chartPushforwardZero_properties x hφ hcφ hφO
  have hη := L18Aux.smoothFn_chartPushforwardZero x hφ hcφ hφO
  have hηc := L18Aux.continuous_of_smoothFn hη
  obtain ⟨D, hD⟩ := hηc.bounded_above_of_compact_support hηp.1
  have hD0 : 0 ≤ D := (norm_nonneg (η x)).trans (hD x)
  let U := multiplyRealForm η A
  have hU := l2RealForm_multiply_bounded g μ η hηc.aestronglyMeasurable D hD0
    (fun y => by simpa only [← Real.norm_eq_abs] using hD y) A hA
  have hm := chartFormPullbackZero_memLp g μ hμ U hU
    (compactlySupportedRealForm_multiply_scalar η hηp.1 A) x
    ((multiplyRealForm_support_subset_scalar η A).trans hηp.2.2)
  apply (memLp_congr_ae ?_).mp hm
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ chartTarget x
    · simp only [chartFormPullbackZero, ite_eq_left hz]
      apply ContinuousAlternatingMap.ext
      intro v
      simp only [U, chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
        multiplyRealForm, ContinuousAlternatingMap.smul_apply, η,
        L18Aux.chartPushforwardZero_chartInv x φ hz]
    · simp only [chartFormPullbackZero, ite_eq_right hz, smul_zero]

theorem chart_cutoff_coord_memLp {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x) (c : α) :
    MemLp (fun z => φ z * b.repr (chartFormPullbackZero x A z) c) 2 (lebesgueC n) := by
  have h := (b.coord c).toContinuousLinearMap.comp_memLp'
    (chart_cutoff_memLp g μ hμ A hA x φ hφ hcφ hφO)
  simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul] using h

/-- Raw chart coordinates have honest integrable compact smooth scalar multiples. -/
theorem chart_cutoff_coord_integrable {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x) (c : α) :
    Integrable (fun z => φ z * b.repr (chartForm A x z) c) (lebesgueC n) := by
  let : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  have hi := memLp_two_compact_integrable (lebesgueC n) _
    (chart_cutoff_coord_memLp g μ hμ A hA x b φ hφ hcφ hφO c) hcφ.mul_right
  apply hi.congr
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ chartTarget x
    · simp only [chartFormPullbackZero, ite_eq_left hz]
    · have hzφ : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
      simp only [hzφ, zero_mul]

/-- Ordinary coordinate first-order coefficient matrix of the actual Hodge expression. -/
def eMatrix {α : Type*} [Fintype α] (g : HermitianField M) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (i : RIdx n) (z : ComplexVector n) (r c : α) : ℝ :=
  b.repr (HodgeJets.E1 g x k i z (b c)) r

/-- Principal divergence coefficient, with row and column first. -/
def a {α : Type*} [Fintype α] [DecidableEq α] (g : HermitianField M) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (r c : α) (i j : RIdx n) (z : ComplexVector n) : ℝ :=
  (realMetricFn g x z)⁻¹ i j * gram g x b z r c

/-- The matrix product H E_i. -/
def T {α : Type*} [Fintype α] [DecidableEq α] (g : HermitianField M) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (r c : α) (i : RIdx n) (z : ComplexVector n) : ℝ :=
  ∑ d, gram g x b z r d * eMatrix g x b i z d c

/-- B_i = -sum_j ∂_j a_ij - (H E_i)^T, in the ordinary coordinate system. -/
def B {α : Type*} [Fintype α] [DecidableEq α] (g : HermitianField M) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (r c : α) (i : RIdx n) (z : ComplexVector n) : ℝ :=
  -(∑ j, fderiv ℝ (a g x b r c i j) z (realModelBasis n j)) - T g x b c r i z

/-- C = (H (E_0 + I))^T; the extra identity is the actual equation's +1. -/
def C {α : Type*} [Fintype α] [DecidableEq α] (g : HermitianField M) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (r c : α) (z : ComplexVector n) : ℝ :=
  (∑ d, gram g x b z c d * b.repr (HodgeJets.E0 g x k z (b r)) d) + gram g x b z c r

theorem eMatrix_contDiffOn {α : Type*} [Fintype α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (i : RIdx n) (r c : α) :
    ContDiffOn ℝ ∞ (fun z => eMatrix g.form x b i z r c) (chartTarget x) := by
  exact (b.coord r).toContinuousLinearMap.contDiff.comp_contDiffOn
    ((HodgeJets.E1_contDiffOn g x k i).clm_apply contDiffOn_const)

theorem a_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (r c : α) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (a g.form x b r c i j) (chartTarget x) :=
  ((L18Aux.realMetricFn_inverse_contDiffOn g x) i j).mul (gram_contDiffOn g x b r c)

theorem T_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (r c : α) (i : RIdx n) :
    ContDiffOn ℝ ∞ (T g.form x b r c i) (chartTarget x) := by
  apply ContDiffOn.sum
  intro d _
  exact (gram_contDiffOn g x b r d).mul (eMatrix_contDiffOn g x b i d c)

theorem B_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (r c : α) (i : RIdx n) :
    ContDiffOn ℝ ∞ (B g.form x b r c i) (chartTarget x) := by
  apply ContDiffOn.sub _ (T_contDiffOn g x b c r i)
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro j _
  exact ((a_contDiffOn g x b r c i j).fderiv_of_isOpen
    (isOpen_extChartAt_target (I := ComplexModel n) x) (by simp)).clm_apply contDiffOn_const

theorem C_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (r c : α) :
    ContDiffOn ℝ ∞ (C g.form x b r c) (chartTarget x) := by
  apply ContDiffOn.add _ (gram_contDiffOn g x b c r)
  apply ContDiffOn.sum
  intro d _
  apply (gram_contDiffOn g x b c d).mul
  exact (b.coord d).toContinuousLinearMap.contDiff.comp_contDiffOn
    ((HodgeJets.E0_contDiffOn g x k).clm_apply contDiffOn_const)

/-- Scalar test differentiation, with no derivatives of the raw input. -/
theorem test_smul_derivative (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (P : Fiber n k) (z v : ComplexVector n) :
    fderiv ℝ (fun y => φ y • P) z v = fderiv ℝ φ z v • P := by
  exact DFunLike.congr_fun ((hφ.differentiable (by simp) z).hasFDerivAt.smul_const P).fderiv v

theorem test_smul_second_derivative (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (P : Fiber n k) (z v w : ComplexVector n) :
    fderiv ℝ (fun y => fderiv ℝ (fun t => φ t • P) y w) z v =
      fderiv ℝ (fun y => fderiv ℝ φ y w) z v • P := by
  have he : (fun y => fderiv ℝ (fun t => φ t • P) y w) =
      fun y => fderiv ℝ φ y w • P := funext fun y => test_smul_derivative φ hφ P y w
  rw [he]
  exact test_smul_derivative _ ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) P z v

/-- Exact scalar row of H(P+1) acting on a fixed basis test. -/
def testRow {α : Type*} [Fintype α] [DecidableEq α] (g : HermitianField M)
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (r c : α)
    (φ : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  -(∑ i, ∑ j, a g x b r c i j z *
    fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z (realModelBasis n j)) +
    (∑ i, T g x b c r i z * fderiv ℝ φ z (realModelBasis n i)) + C g x b r c z * φ z

/-- Symmetry of the genuine compact smooth test Hessian fixes the divergence indices. -/
theorem scalar_hessian_symm (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (z v w : ComplexVector n) :
    fderiv ℝ (fun y => fderiv ℝ φ y w) z v =
      fderiv ℝ (fun y => fderiv ℝ φ y v) z w := by
  have hs : IsSymmSndFDerivAt ℝ φ z := hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have he (v w : ComplexVector n) : fderiv ℝ (fun y => fderiv ℝ φ y w) z v =
      fderiv ℝ (fderiv ℝ φ) z v w := by
    exact DFunLike.congr_fun ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z hd.hasFDerivAt).fderiv v
  rw [he, he]
  exact hs v w

set_option maxHeartbeats 1200000 in
theorem testRow_mulVec {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (r c : α) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : ComplexVector n) :
    (gram g x b z).mulVec
      (b.repr (testOperator g x (fun y => φ y • b r) z + φ z • b r)) c =
      testRow g x b r c φ z := by
  classical
  have hsym (i j : RIdx n) := scalar_hessian_symm φ hφ z (realModelBasis n i) (realModelBasis n j)
  unfold testOperator
  simp_rw [test_smul_second_derivative φ hφ]
  simp only [Matrix.mulVec, dotProduct, test_smul_derivative φ hφ,
    map_add, map_neg, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul,
    Basis.repr_self, mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hp : (∑ d, gram g x b z c d *
      ∑ i, ∑ j, (realMetricFn g x z)⁻¹ i j *
        (fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n j)) z (realModelBasis n i) *
          (Finsupp.single r (1 : ℝ)) d)) =
      ∑ i, ∑ j, a g x b r c i j z *
        fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z (realModelBasis n j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp [a, Finsupp.single_apply, gram_symm, hsym, mul_comm, mul_left_comm, mul_assoc]
  have hfirst : (∑ d, gram g x b z c d *
      ∑ i, fderiv ℝ φ z (realModelBasis n i) * b.repr (HodgeJets.E1 g x k i z (b r)) d) =
      ∑ i, T g x b c r i z * fderiv ℝ φ z (realModelBasis n i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [T, eMatrix, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hp, hfirst]
  simp only [testRow, C]
  simp only [Finsupp.single_apply]
  simp [mul_add, mul_comm, mul_left_comm, Finset.mul_sum]
  ring

theorem testRow_pairing {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (P : Fiber n k) (r : α) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (z : ComplexVector n) :
    dotProduct (b.repr P) ((gram g x b z).mulVec
      (b.repr (testOperator g x (fun y => φ y • b r) z + φ z • b r))) =
      ∑ c, b.repr P c * testRow g x b r c φ z := by
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro c _
  rw [testRow_mulVec g x b r c φ hφ]

/-- The compact scalar row vanishes outside its genuine test support. -/
theorem testRow_zero_off {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (r c : α) (φ : ComplexVector n → ℝ) (z : ComplexVector n)
    (hz : z ∉ tsupport φ) : testRow g x b r c φ z = 0 := by
  have hφz := image_eq_zero_of_notMem_tsupport hz
  have hd := fderiv_of_notMem_tsupport ℝ hz
  have hdd (i : RIdx n) : fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun h => hz ((tsupport_fderiv_apply_subset ℝ _) h))
  simp only [testRow, hd, hdd, zero_apply, hφz, mul_zero,
    Finset.sum_const_zero, neg_zero, add_zero]

/-- The original Hodge maximal graph gives every ordinary-coordinate scalar row. -/
theorem maximalGraph_chart_scalar_test {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) (r : α)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    (∫ z, ∑ c, b.repr (chartForm A x z) c * testRow g.form x b r c φ z ∂lebesgueC n) = 0 := by
  let G := fun z => φ z • b r
  have hs : tsupport G ⊆ tsupport φ := tsupport_smul_subset_left φ _
  have h := maximalGraph_chart_vector_test g μ hμ A hmax x b G (hφ.smul contDiff_const)
    (hcφ.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hφO)
  have he : (fun z => dotProduct (b.repr (chartForm A x z))
      ((gram g.form x b z).mulVec (b.repr (testOperator g.form x G z + G z)))) =
      fun z => ∑ c, b.repr (chartForm A x z) c * testRow g.form x b r c φ z := by
    funext z
    exact testRow_pairing g.form x b (chartForm A x z) r φ hφ z
  rw [he] at h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at h
  · exact h
  · intro z hz
    apply Finset.sum_eq_zero
    intro c _
    rw [testRow_zero_off g.form x b r c φ z (fun h => hz (hφO h)), mul_zero]

/-- Any smooth chart coefficient times a compact smooth scalar test can be
paired integrably with a raw coordinate. -/
theorem coord_test_integrable {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (x : M.Carrier)
    (b : Basis α ℝ (Fiber n k)) (c : α) (q ψ : ComplexVector n → ℝ)
    (hq : ContDiffOn ℝ ∞ q (chartTarget x)) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hψO : tsupport ψ ⊆ chartTarget x) :
    Integrable (fun z => b.repr (chartForm A x z) c * (q z * ψ z)) (lebesgueC n) := by
  have hp := scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
    ψ hψ hcψ hψO q hq
  have hi := chart_cutoff_coord_integrable g μ hμ A hA x b _ hp.1 hp.2.1 (hp.2.2.trans hψO) c
  apply hi.congr
  exact Filter.Eventually.of_forall fun z => by ring

/-- A genuine formal-transpose divergence weak equation, expressed solely using
test derivatives, coefficient derivatives, and undifferentiated raw coordinates. -/
def DivergenceWeak {α : Type*} [Fintype α]
    (u : ComplexVector n → α → ℝ) (O : Set (ComplexVector n))
    (a : α → α → RIdx n → RIdx n → ComplexVector n → ℝ)
    (B : α → α → RIdx n → ComplexVector n → ℝ)
    (C : α → α → ComplexVector n → ℝ) : Prop :=
  ∀ r (φ : ComplexVector n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
    (∑ c, (-(∑ i, ∑ j, ∫ z, u z c *
      (a r c i j z * fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z (realModelBasis n j) +
       fderiv ℝ (a r c i j) z (realModelBasis n j) * fderiv ℝ φ z (realModelBasis n i)) ∂lebesgueC n) -
      (∑ i, ∫ z, u z c * B r c i z * fderiv ℝ φ z (realModelBasis n i) ∂lebesgueC n) +
      ∫ z, u z c * C r c z * φ z ∂lebesgueC n)) = 0

/-- The divergence test expression cancels to the exact scalar row of H(P+1). -/
theorem divergence_row_identity {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (r c : α) (φ : ComplexVector n → ℝ) (z : ComplexVector n) (v : ℝ) :
    v * testRow g x b r c φ z =
      -(∑ i, ∑ j, v * (a g x b r c i j z *
        fderiv ℝ (fun y => fderiv ℝ φ y (realModelBasis n i)) z (realModelBasis n j) +
        fderiv ℝ (a g x b r c i j) z (realModelBasis n j) * fderiv ℝ φ z (realModelBasis n i))) -
      (∑ i, v * B g x b r c i z * fderiv ℝ φ z (realModelBasis n i)) +
      v * C g x b r c z * φ z := by
  simp only [testRow, B, mul_add, mul_neg, mul_sub, neg_mul, sub_mul,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, mul_assoc]
  ring

set_option maxHeartbeats 1500000 in
/-- The original actual Hodge maximal equation is the ordinary-coordinate
formal-transpose divergence equation in every genuine chart. No derivative of A occurs. -/
theorem maximalGraph_divergenceWeak {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k)) :
    DivergenceWeak (fun z c => b.repr (chartForm A x z) c) (chartTarget x)
      (a g.form x b) (B g.form x b) (C g.form x b) := by
  classical
  intro r φ hφ hcφ hφO
  let u := fun z c => b.repr (chartForm A x z) c
  let dφ := fun i z => fderiv ℝ φ z (realModelBasis n i)
  let ddφ := fun i j z => fderiv ℝ (dφ i) z (realModelBasis n j)
  let p := fun c i j z => u z c * (a g.form x b r c i j z * ddφ i j z +
    fderiv ℝ (a g.form x b r c i j) z (realModelBasis n j) * dφ i z)
  let q := fun c i z => u z c * B g.form x b r c i z * dφ i z
  let v := fun c z => u z c * C g.form x b r c z * φ z
  have hd (i : RIdx n) : ContDiff ℝ ∞ (dφ i) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcD (i : RIdx n) : HasCompactSupport (dφ i) := hcφ.fderiv_apply ℝ (realModelBasis n i)
  have hsD (i : RIdx n) : tsupport (dφ i) ⊆ chartTarget x :=
    (tsupport_fderiv_apply_subset ℝ (realModelBasis n i)).trans hφO
  have hdd (i j : RIdx n) : ContDiff ℝ ∞ (ddφ i j) :=
    ((hd i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcDD (i j : RIdx n) : HasCompactSupport (ddφ i j) :=
    (hcD i).fderiv_apply ℝ (realModelBasis n j)
  have hsDD (i j : RIdx n) : tsupport (ddφ i j) ⊆ chartTarget x :=
    (tsupport_fderiv_apply_subset ℝ (realModelBasis n j)).trans (hsD i)
  have hp (c : α) (i j : RIdx n) : Integrable (p c i j) (lebesgueC n) := by
    have h1 := coord_test_integrable g μ hμ A hmax.1 x b c _ _
      (a_contDiffOn g x b r c i j) (hdd i j) (hcDD i j) (hsDD i j)
    have hda : ContDiffOn ℝ ∞
        (fun z => fderiv ℝ (a g.form x b r c i j) z (realModelBasis n j)) (chartTarget x) :=
      ((a_contDiffOn g x b r c i j).fderiv_of_isOpen
        (isOpen_extChartAt_target (I := ComplexModel n) x) (by simp)).clm_apply contDiffOn_const
    have h2 := coord_test_integrable g μ hμ A hmax.1 x b c _ _ hda (hd i) (hcD i) (hsD i)
    apply (h1.add h2).congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [p, u, Pi.add_apply]; ring
  have hq (c : α) (i : RIdx n) : Integrable (q c i) (lebesgueC n) := by
    have hi := coord_test_integrable g μ hμ A hmax.1 x b c _ _
      (B_contDiffOn g x b r c i) (hd i) (hcD i) (hsD i)
    apply hi.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [q, u]; ring
  have hv (c : α) : Integrable (v c) (lebesgueC n) := by
    have hi := coord_test_integrable g μ hμ A hmax.1 x b c _ _
      (C_contDiffOn g x b r c) hφ hcφ hφO
    apply hi.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [v, u]; ring
  have hpj (c : α) (i : RIdx n) : Integrable (fun z => ∑ j, p c i j z) (lebesgueC n) :=
    integrable_finsetSum Finset.univ (fun j _ => hp c i j)
  have hpij (c : α) : Integrable (fun z => ∑ i, ∑ j, p c i j z) (lebesgueC n) :=
    integrable_finsetSum Finset.univ (fun i _ => hpj c i)
  have hqi (c : α) : Integrable (fun z => ∑ i, q c i z) (lebesgueC n) :=
    integrable_finsetSum Finset.univ (fun i _ => hq c i)
  have he (c : α) : (fun z => u z c * testRow g.form x b r c φ z) =
      fun z => -(∑ i, ∑ j, p c i j z) - (∑ i, q c i z) + v c z := by
    funext z
    exact divergence_row_identity g.form x b r c φ z (u z c)
  have hrowi (c : α) : Integrable (fun z => u z c * testRow g.form x b r c φ z) (lebesgueC n) := by
    rw [he c]
    exact (((hpij c).neg).sub (hqi c)).add (hv c)
  have hneg (c : α) : Integrable (fun z => -(∑ i, ∑ j, p c i j z)) (lebesgueC n) :=
    (hpij c).neg
  have hsub (c : α) : Integrable (fun z => -(∑ i, ∑ j, p c i j z) - (∑ i, q c i z)) (lebesgueC n) :=
    (hneg c).sub (hqi c)
  have hrowint (c : α) : (∫ z, u z c * testRow g.form x b r c φ z ∂lebesgueC n) =
      -(∑ i, ∑ j, ∫ z, p c i j z ∂lebesgueC n) -
      (∑ i, ∫ z, q c i z ∂lebesgueC n) + ∫ z, v c z ∂lebesgueC n := by
    rw [he c, integral_add (hsub c) (hv c),
      integral_sub (hneg c) (hqi c), integral_neg,
      integral_finsetSum Finset.univ (fun i _ => hpj c i),
      integral_finsetSum Finset.univ (fun i _ => hq c i)]
    simp_rw [integral_finsetSum Finset.univ (fun j _ => hp c _ j)]
  have h := maximalGraph_chart_scalar_test g μ hμ A hmax x b r φ hφ hcφ hφO
  change (∫ z, ∑ c, u z c * testRow g.form x b r c φ z ∂lebesgueC n) = 0 at h
  rw [integral_finsetSum Finset.univ (fun c _ => hrowi c)] at h
  simp_rw [hrowint] at h
  exact h

/-- The actual volume-weighted Gram is positive definite in its genuine chart. -/
theorem gram_posDef {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    {z : ComplexVector n} (hz : z ∈ chartTarget x) : (gram g x b z).PosDef := by
  let Q := Real.sqrt (realMetricFn g x z).det • modelFormMetricBilin g x z k
  have hS : Q.IsSymm := by
    refine ⟨?_⟩
    intro P R
    change Real.sqrt (realMetricFn g x z).det * modelFormInner (realMetricFn g x z)⁻¹ P R =
      Real.sqrt (realMetricFn g x z).det * modelFormInner (realMetricFn g x z)⁻¹ R P
    rw [modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) P R]
  have hP : Q.toQuadraticMap.PosDef := by
    intro P hP
    change 0 < Real.sqrt (realMetricFn g x z).det * modelFormInner (realMetricFn g x z)⁻¹ P P
    exact mul_pos (Real.sqrt_pos.mpr (realMetricFn_posDef_of_mem_target g x hz).det_pos)
      (modelFormInner_self_pos g x hz P hP)
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b Q hS).mp hP

/-- Both the physical inverse metric and the volume Gram have their required symmetries. -/
theorem a_symmetries {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (r c : α) (i j : RIdx n) (z : ComplexVector n) :
    a g x b r c i j z = a g x b c r i j z ∧
    a g x b r c i j z = a g x b r c j i z := by
  constructor
  · simp only [a, gram_symm g x b z r c]
  · have hs := congrFun (congrFun (realMetricFn_inv_isSymm g x z) j) i
    change (realMetricFn g x z)⁻¹ i j = (realMetricFn g x z)⁻¹ j i at hs
    simp only [a, hs]

theorem testOperator_zero_off (g : HermitianField M) (x : M.Carrier)
    (G : ComplexVector n → Fiber n k) (z : ComplexVector n) (hz : z ∉ tsupport G) :
    testOperator g x G z = 0 := by
  have hGz := image_eq_zero_of_notMem_tsupport hz
  have hd := fderiv_of_notMem_tsupport ℝ hz
  have hdd (j : RIdx n) : fderiv ℝ (fun y => fderiv ℝ G y (realModelBasis n j)) z = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun h => hz ((tsupport_fderiv_apply_subset ℝ _) h))
  simp only [testOperator, hd, hdd, zero_apply, hGz, map_zero,
    smul_zero, Finset.sum_const_zero, neg_zero, add_zero]

/-- The weighted vector equation over all ordinary coordinate space; the genuine
compact test and all its derivatives vanish off the chart. -/
theorem maximalGraph_chart_vector_test_global {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (G : ComplexVector n → Fiber n k) (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x) :
    (∫ z, dotProduct (b.repr (chartForm A x z))
      ((gram g.form x b z).mulVec (b.repr (testOperator g.form x G z + G z))) ∂lebesgueC n) = 0 := by
  have h := maximalGraph_chart_vector_test g μ hμ A hmax x b G hG hcG hGO
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at h
  · exact h
  · intro z hz
    have hzs : z ∉ tsupport G := fun h => hz (hGO h)
    simp only [testOperator_zero_off g.form x G z hzs,
      image_eq_zero_of_notMem_tsupport hzs, add_zero, map_zero,
      Finsupp.coe_zero, Matrix.mulVec_zero, dotProduct_zero]

end Yau.LeafProofs.L03.HodgeDivergenceWeak
