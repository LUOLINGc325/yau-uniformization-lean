import spec.CHAIN.LeafObligations
import Yau.LeafProofs.SharedCalculus
import Yau.LeafProofs.L09
import Yau.LeafProofs.L12

/-!
Internal infrastructure for the complete Li--Schoen mean-value obligation.
The geometric mean-value estimate is not assumed in this file.
-/

open MeasureTheory Filter
open scoped Topology ContDiff Manifold ENNReal Matrix ComplexOrder

noncomputable section

namespace Yau.LeafProofs.L18Aux

/-- The chartwise real smoothness used in the leaf implies continuity in the
original manifold topology. -/
theorem continuous_of_smoothFn {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : ContinuousAt (inChart x u) (chartPt x x) :=
    (hu x).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (mem_extChartAt_target x))
  have hcomp := hc.comp (continuousAt_extChartAt (I := ComplexModel n) x)
  apply hcomp.congr
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_source x)] with y hy
  exact congrArg u ((extChartAt (ComplexModel n) x).left_inv hy)

/-- In particular, the nonnegative integrand occurring in the exact L18 root
is measurable for the fixed Borel measurable structure. -/
theorem measurable_ofReal_of_smoothFn {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) :
    Measurable (fun x => ENNReal.ofReal (u x)) :=
  ENNReal.measurable_ofReal.comp (continuous_of_smoothFn hu).measurable

/-- Smoothness on the open chart target gives ordinary derivatives at each
chart point, so no within-derivative can silently replace the leaf's operators. -/
theorem contDiffAt_inChart {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    ContDiffAt ℝ ∞ (inChart x u) z :=
  (hu x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)

/-- Differentiate the actual barred Wirtinger operator over the real scalar
field. The derivative exists because the first Fréchet derivative does. -/
theorem fderiv_wirtBar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} {z : E}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) z) (v w : E) :
    fderiv ℝ (fun y => wirtBar F y v) z w =
      (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ F) z w v +
        Complex.I * fderiv ℝ (fderiv ℝ F) z w (Complex.I • v)) := by
  have hv : DifferentiableAt ℝ (fun y => fderiv ℝ F y v) z :=
    hF.clm_apply (differentiableAt_const v)
  have hIv : DifferentiableAt ℝ (fun y => fderiv ℝ F y (Complex.I • v)) z :=
    hF.clm_apply (differentiableAt_const (Complex.I • v))
  simp only [wirtBar]
  rw [fderiv_const_mul (hv.fun_add (hIv.const_mul Complex.I)),
    fderiv_fun_add hv (hIv.const_mul Complex.I), fderiv_const_mul hIv,
    fderiv_clm_apply hF (differentiableAt_const v),
    fderiv_clm_apply hF (differentiableAt_const (Complex.I • v))]
  simp
  ring

/-- Expanding the leaf's nested Wirtinger definition gives a quarter of four
real second derivatives, before using that the function is real valued. -/
theorem wirt_wirtBar_eq_secondFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} {z : E}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) z) (v w : E) :
    wirt (fun y => wirtBar F y v) z w =
      (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ F) z w v +
        fderiv ℝ (fderiv ℝ F) z (Complex.I • w) (Complex.I • v) +
        Complex.I * (fderiv ℝ (fderiv ℝ F) z w (Complex.I • v) -
          fderiv ℝ (fderiv ℝ F) z (Complex.I • w) v)) := by
  rw [wirt, fderiv_wirtBar hF, fderiv_wirtBar hF]
  linear_combination -(1 / 4 : ℂ) *
    fderiv ℝ (fderiv ℝ F) z (Complex.I • w) (Complex.I • v) * Complex.I_sq

/-- Complexifying a real function complexifies its real Hessian. This is an
identity for the actual nested Fréchet derivatives, on a neighborhood of `z`. -/
theorem secondFDeriv_ofReal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (f y : ℂ))) z w v =
      (fderiv ℝ (fderiv ℝ f) z w v : ℂ) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF : DifferentiableAt ℝ (fderiv ℝ (fun y => (f y : ℂ))) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun y => (f y : ℂ)) y v) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ f y v : ℂ)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    have hd := hy.differentiableAt (by norm_num)
    change fderiv ℝ (Complex.ofRealCLM ∘ f) y v = _
    rw [fderiv_comp y Complex.ofRealCLM.differentiableAt hd]
    simp
  have h := congrArg (fun L : E →L[ℝ] ℂ => L w) heq.fderiv_eq
  rw [fderiv_clm_apply hdF (differentiableAt_const v)] at h
  change _ = fderiv ℝ (Complex.ofRealCLM ∘ (fun y => fderiv ℝ f y v)) z w at h
  rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
    (hdf.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply hdf (differentiableAt_const v)] at h
  simpa using h

/-- For real functions each diagonal Levi entry has real part equal to one
quarter of the two corresponding ordinary real second derivatives. -/
theorem leviMatrix_diag_re
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (dir : ι → E) (i : ι) :
    (leviMatrix f z dir i i).re = (1 / 4 : ℝ) *
      (fderiv ℝ (fderiv ℝ f) z (dir i) (dir i) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • dir i) (Complex.I • dir i)) := by
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [leviMatrix, wirt_wirtBar_eq_secondFDeriv hdF]
  simp only [secondFDeriv_ofReal hf, Complex.mul_re, Complex.add_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  norm_num

/-- Young absorption in the exact form used to pass from squared supremum
estimates to an affine recurrence. -/
theorem quadratic_absorption {m t K ε : ℝ}
    (hm : 0 ≤ m) (ht : 0 ≤ t) (hK : 0 ≤ K) (hε : 0 < ε)
    (h : m ^ 2 ≤ K * t) : m ≤ ε * t + K / (4 * ε) := by
  have hcross : 4 * (ε * t) * (K / (4 * ε)) = K * t := by
    field_simp
  have hrhs : 0 ≤ ε * t + K / (4 * ε) := by positivity
  have hsq : m ^ 2 ≤ (ε * t + K / (4 * ε)) ^ 2 := by
    nlinarith [sq_nonneg (ε * t - K / (4 * ε))]
  exact (sq_le_sq₀ hm hrhs).mp hsq

/-- A complete dyadic iteration, including removal of its bounded terminal
term. This is the numerical L¹ interpolation step, independent of geometry. -/
theorem bounded_dyadic_iteration (s : ℕ → ℝ) {q A B : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A)
    (hbound : ∀ i, s i ≤ B)
    (hstep : ∀ i, q ^ i * s i ≤
      q ^ (i + 1) * s (i + 1) + A * (1 / 2 : ℝ) ^ i) :
    s 0 ≤ 2 * A := by
  have hfinite (N : ℕ) : s 0 ≤ q ^ N * s N +
      A * ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      nlinarith [hstep N]
  have hfinal (N : ℕ) : s 0 ≤ q ^ N * B + 2 * A := by
    have htail := mul_le_mul_of_nonneg_left (hbound N) (pow_nonneg hq N)
    have hsum := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hA
    linarith [hfinite N]
  have hlim : Tendsto (fun N : ℕ => q ^ N * B + 2 * A) atTop (𝓝 (2 * A)) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const B).add_const (2 * A)
  exact ge_of_tendsto' hlim hfinal

/-- The p=1 Li--Schoen interpolation recurrence closes with a constant
depending only on its two quantitative coefficients, with no residual
supremum or boundedness constant in the conclusion. -/
theorem bounded_quadratic_iteration (s : ℕ → ℝ) {b K B : ℝ}
    (hb : 1 ≤ b) (hK : 0 ≤ K) (hs : ∀ i, 0 ≤ s i)
    (hbound : ∀ i, s i ≤ B)
    (hstep : ∀ i, (s i) ^ 2 ≤ K * b ^ i * s (i + 1)) :
    s 0 ≤ b * K := by
  let q : ℝ := 1 / (2 * b)
  let A : ℝ := b * K / 2
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * b)).mpr
    linarith
  have hqb : q * b = (1 / 2 : ℝ) := by dsimp [q]; field_simp
  have hcoef (i : ℕ) : K * b ^ i / (4 * q) = A * b ^ i := by
    dsimp [q, A]
    field_simp
    ring
  have hrec (i : ℕ) : q ^ i * s i ≤
      q ^ (i + 1) * s (i + 1) + A * (1 / 2 : ℝ) ^ i := by
    have hi := quadratic_absorption (hs i) (hs (i + 1))
      (mul_nonneg hK (pow_nonneg hb0.le i)) hq0 (hstep i)
    rw [hcoef] at hi
    have him := mul_le_mul_of_nonneg_left hi (pow_nonneg hq0.le i)
    convert him using 1
    rw [← hqb, mul_pow, pow_succ]
    ring
  have h := bounded_dyadic_iteration s hq0.le hq1
    (by dsimp [A]; positivity) hbound hrec
  dsimp [A] at h
  linarith

/-- The actual inverse-chart differential preserves complex scalars. -/
theorem chartVec_smul {n : ℕ} {M : ComplexManifold n}
    (x y : M.Carrier) (c : ℂ) (v : ComplexVector n) :
    chartVec x y (c • v) = c • chartVec x y v := by
  exact (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)).map_smul c v

theorem chartVec_sum {n : ℕ} {M : ComplexManifold n} {ι : Type*}
    (x y : M.Carrier) (s : Finset ι) (v : ι → ComplexVector n) :
    chartVec x y (∑ i ∈ s, v i) = ∑ i ∈ s, chartVec x y (v i) := by
  exact map_sum (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)) v s

/-- The real metric entries come from the actual complex-linear chart
derivative and Hermitian sesquilinearity. This also fixes the off-diagonal
signs in the realification. -/
theorem realMetricFn_entries {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b : RIdx n) :
    realMetricFn h x z a b = 2 *
      (if a.2 = b.2 then (hMat h x z a.1 b.1).re
        else if a.2 = 0 then -(hMat h x z a.1 b.1).im
        else (hMat h x z a.1 b.1).im) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realMetricFn, realVec, hMat, stdVec, chartVec_smul,
      HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right]

/-- No extra Hermitian assumption is needed for the chart Gram matrix. -/
theorem hMat_isHermitian {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (hMat h x z).IsHermitian := by
  ext i j
  exact ((h (chartInv x z)).conjugate_symmetric _ _).symm

/-- Squaring a bounded nonnegative integrand costs only one copy of its
bound; this is the measure-theoretic input to p=1 interpolation. -/
theorem setLIntegral_sq_le_bound_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : Measurable f) (s : Set α) (B : ℝ≥0∞)
    (hB : ∀ x ∈ s, f x ≤ B) :
    ∫⁻ x in s, f x ^ 2 ∂μ ≤ B * ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_const_mul B hf]
  exact setLIntegral_mono (measurable_const.mul hf) fun x hx => by
    simpa only [pow_two] using mul_le_mul_left (hB x hx) (f x)

/-- Sesquilinearity commutes with the finite sums used by Gram matrices. -/
theorem hermitian_sum_left {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : ι → V) (v : V) :
    h.toFun (∑ i ∈ s, u i) v = ∑ i ∈ s, h.toFun (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_left (0 : ℂ) (0 : V) v
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_left, ih]

theorem hermitian_sum_right {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : V) (v : ι → V) :
    h.toFun u (∑ i ∈ s, v i) = ∑ i ∈ s, h.toFun u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_right (0 : ℂ) u (0 : V)
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_right, ih]

/-- The actual chart Gram quadratic form equals the intrinsic Hermitian
value of the reconstructed vector. -/
theorem hMat_quadratic {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (u : Fin n → ℂ) :
    star u ⬝ᵥ ((hMat h x z) *ᵥ u) =
      (h (chartInv x z)).toFun
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i))
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i)) := by
  rw [hermitian_sum_left]
  simp only [hermitian_sum_right,
    HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, hMat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The inverse chart differential is injective throughout its source. -/
theorem chartVec_injective {n : ℕ} {M : ComplexManifold n}
    (x y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    Function.Injective (chartVec x y) := by
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  have hleft : Function.LeftInverse (tangentCoords x y) (chartVec x y) := by
    intro v
    have hv := congrArg (fun L => L v) hcomp
    change tangentCoords x y (chartVec x y v) = v at hv
    exact hv
  exact hleft.injective

/-- Hence the leaf's chart metric matrices really are positive definite;
the totalized matrix inverse is used only on genuine invertible matrices. -/
theorem hMat_posDef {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) : (hMat h x z).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hMat_isHermitian h x z)
  intro u hu
  rw [hMat_quadratic]
  apply Complex.pos_iff.mpr
  refine ⟨hermitianNormSq_pos (h (chartInv x z)) ?_,
    ((h (chartInv x z)).self_adjoint _).symm⟩
  intro hzero
  have hsum : ∑ i, u i • stdVec i = (WithLp.toLp 2 u : ComplexVector n) := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have heq : ∑ i, u i • chartVec x (chartInv x z) (stdVec i) =
      chartVec x (chartInv x z) (WithLp.toLp 2 u) := by
    rw [← hsum, chartVec_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (chartVec_smul _ _ _ _).symm
  rw [heq] at hzero
  have hzsource := (extChartAt (ComplexModel n) x).map_target hz
  have hzero' : chartVec x (chartInv x z) (WithLp.toLp 2 u) =
      chartVec x (chartInv x z) 0 := by
    have hzv : chartVec x (chartInv x z) 0 = 0 := by
      simpa using chartVec_smul x (chartInv x z) 0 0
    simpa only [hzv] using hzero
  have hu0 := chartVec_injective x (chartInv x z) hzsource hzero'
  apply hu
  ext i
  simpa using congrArg (fun v : ComplexVector n => v i) hu0

/-- The two independently written coordinate metric calculators agree by
their definitions, including the same fixed chart frame. -/
theorem hMat_eq_chartCoefficientFunction {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (i j : Fin n) :
    hMat h x z i j = chartCoefficientFunction h x i j z := by
  rfl

theorem hMat_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => hMat g.form x z i j) (chartTarget x) := by
  simpa only [hMat_eq_chartCoefficientFunction, chartTarget] using
    g.coordinate_smooth x i j

/-- Coordinate smoothness of the supplied Hermitian metric gives smoothness
of its actual real Riemannian coefficient matrix. -/
theorem metricSmooth_of_smoothMetric {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) : MetricSmooth g.form := by
  intro x a b
  simp_rw [realMetricFn_entries]
  split_ifs
  · exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
      (hMat_contDiffOn g x a.1 b.1))
  · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (hMat_contDiffOn g x a.1 b.1)).neg
  · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (hMat_contDiffOn g x a.1 b.1))

/-- Determinants are finite polynomial expressions in their entries. -/
theorem contDiffOn_matrix_det {E ι 𝔸 : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {A : E → Matrix ι ι 𝔸} {s : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) s) :
    ContDiffOn ℝ ∞ (fun z => (A z).det) s :=
  SharedCalculus.contDiffOn_matrix_det hA

/-- The logarithm in the actual complex Ricci calculator never evaluates at
zero on the chart target. -/
theorem hMat_det_re_pos {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) : 0 < (hMat h x z).det.re :=
  (Complex.pos_iff.mp (hMat_posDef h x z hz).det_pos).1

theorem logDet_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (logDet g.form x) (chartTarget x) := by
  have hd : ContDiffOn ℝ ∞ (fun z => (hMat g.form x z).det.re) (chartTarget x) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (contDiffOn_matrix_det (hMat_contDiffOn g x))
  exact hd.log fun z hz => ne_of_gt (hMat_det_re_pos g.form x hz)

/-- Continuity of the exact density used by `IsRiemannianVolume`, without
using the still separate determinant normalization identity. -/
theorem volumeDensity_continuousOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) :
    ContinuousOn (fun z => Real.sqrt (realMetricFn g.form x z).det) (chartTarget x) :=
  (contDiffOn_matrix_det (metricSmooth_of_smoothMetric g x)).continuousOn.sqrt

/-- The chart law in the exact leaf forces local finiteness of volume.
Its proof uses an actual bounded-density coordinate neighborhood. -/
theorem riemannianVolume_locallyFinite {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : IsLocallyFiniteMeasure μ := by
  constructor
  intro x
  let d : ComplexVector n → ℝ := fun z => Real.sqrt (realMetricFn g.form x z).det
  let z₀ : ComplexVector n := chartPt x x
  let B : ℝ := d z₀ + 1
  have hz₀ : z₀ ∈ chartTarget x := mem_extChartAt_target x
  have htarget : chartTarget x ∈ 𝓝 z₀ :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz₀
  have hd : ContinuousAt d z₀ :=
    (volumeDensity_continuousOn g x).continuousAt htarget
  have hB : {z | d z < B} ∈ 𝓝 z₀ :=
    hd.preimage_mem_nhds (Iio_mem_nhds (by dsimp [B]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hB)
  let s : Set M.Carrier := (extChartAt (ComplexModel n) x).source ∩
    chartPt x ⁻¹' Metric.ball z₀ ε
  have hs : IsOpen s :=
    isOpen_extChartAt_preimage' (I := ComplexModel n) x Metric.isOpen_ball
  have hxs : x ∈ s := ⟨mem_extChartAt_source x, Metric.mem_ball_self hε⟩
  refine ⟨s, hs.mem_nhds hxs, ?_⟩
  have hsource : s ⊆ (chartAt (ComplexVector n) x).source := by
    intro y hy
    simpa only [extChartAt_source] using hy.1
  rw [hμ x s hs.measurableSet hsource]
  have himage : chartPt x '' s ⊆ Metric.ball z₀ ε := by
    rintro z ⟨y, hy, rfl⟩
    exact hy.2
  have hmass : lebesgueC n (Metric.closedBall z₀ ε) < ⊤ := by
    rw [lebesgueC_eq_volume]
    exact (isCompact_closedBall z₀ ε).measure_lt_top
  calc
    ∫⁻ z in chartPt x '' s, ENNReal.ofReal (d z) ∂lebesgueC n
        ≤ ∫⁻ z in chartPt x '' s, ENNReal.ofReal B ∂lebesgueC n :=
      setLIntegral_mono measurable_const fun z hz =>
        ENNReal.ofReal_le_ofReal (hball (himage hz)).2.le
    _ = ENNReal.ofReal B * lebesgueC n (chartPt x '' s) := by simp
    _ ≤ ENNReal.ofReal B * lebesgueC n (Metric.closedBall z₀ ε) :=
      mul_le_mul_right (measure_mono
        (himage.trans Metric.ball_subset_closedBall)) (ENNReal.ofReal B)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass

/-- A smooth scalar is integrable on every compact set for the exact volume
measure in the root. -/
theorem smoothFn_integrableOn_compact {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) {K : Set M.Carrier} (hK : IsCompact K) :
    IntegrableOn u K μ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  exact (continuous_of_smoothFn hu).continuousOn.integrableOn_compact hK

/-- Real-integral version of the bounded-square estimate. -/
theorem integral_sq_le_bound_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {s : Set α} (hs : MeasurableSet s)
    {u : α → ℝ} (hu : IntegrableOn u s μ)
    (hu2 : IntegrableOn (fun x => u x ^ 2) s μ) {B : ℝ}
    (h0 : ∀ x ∈ s, 0 ≤ u x) (hB : ∀ x ∈ s, u x ≤ B) :
    ∫ x in s, u x ^ 2 ∂μ ≤ B * ∫ x in s, u x ∂μ := by
  have h := setIntegral_mono_on hu2 (hu.const_mul B) hs fun x hx => by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hB x hx) (h0 x hx)
  simpa only [integral_const_mul] using h

/-- The complete passage from local L² supremum estimates to an L¹
estimate on the specified sets. The displayed L² input remains a separate
geometric proof obligation when applying this lemma to L18. -/
theorem L2_to_L1_interpolation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u : α → ℝ) (S : ℕ → Set α) (T : Set α)
    (hS : ∀ i, MeasurableSet (S i)) (hSne : ∀ i, (S i).Nonempty)
    (hST : ∀ i, S i ⊆ T) (h0 : ∀ x, 0 ≤ u x)
    (hu : IntegrableOn u T μ)
    (hu2 : ∀ i, IntegrableOn (fun x => u x ^ 2) (S i) μ)
    (hbdd : BddAbove (u '' T)) {A b : ℝ} (hA : 0 ≤ A) (hb : 1 ≤ b)
    (hL2 : ∀ i, (sSup (u '' S i)) ^ 2 ≤
      A * b ^ i * ∫ x in S (i + 1), u x ^ 2 ∂μ) :
    ∀ x ∈ S 0, u x ≤ b * A * ∫ y in T, u y ∂μ := by
  let s : ℕ → ℝ := fun i => sSup (u '' S i)
  let I : ℝ := ∫ y in T, u y ∂μ
  have hI : 0 ≤ I := integral_nonneg h0
  have hbddi (i : ℕ) : BddAbove (u '' S i) :=
    hbdd.mono (Set.image_mono (hST i))
  have husi (i : ℕ) (x : α) (hx : x ∈ S i) : u x ≤ s i :=
    le_csSup (hbddi i) (Set.mem_image_of_mem u hx)
  have hs0 (i : ℕ) : 0 ≤ s i := by
    obtain ⟨x, hx⟩ := hSne i
    exact (h0 x).trans (husi i x hx)
  obtain ⟨B, hB⟩ := hbdd
  have hbound (i : ℕ) : s i ≤ B := by
    apply csSup_le ((hSne i).image u)
    rintro a ⟨x, hx, rfl⟩
    exact hB (Set.mem_image_of_mem u (hST i hx))
  have henergy (i : ℕ) : ∫ x in S i, u x ^ 2 ∂μ ≤ s i * I := by
    calc
      ∫ x in S i, u x ^ 2 ∂μ ≤ s i * ∫ x in S i, u x ∂μ :=
        integral_sq_le_bound_mul μ (hS i) (hu.mono_set (hST i)) (hu2 i)
          (fun x _ => h0 x) (husi i)
      _ ≤ s i * I := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hu (ae_of_all _ h0) (ae_of_all _ (hST i))) (hs0 i)
  have hrec (i : ℕ) : (s i) ^ 2 ≤ (A * I) * b ^ i * s (i + 1) := by
    calc
      (s i) ^ 2 ≤ A * b ^ i * ∫ x in S (i + 1), u x ^ 2 ∂μ := hL2 i
      _ ≤ A * b ^ i * (s (i + 1) * I) :=
        mul_le_mul_of_nonneg_left (henergy (i + 1))
          (mul_nonneg hA (pow_nonneg (le_trans zero_le_one hb) i))
      _ = (A * I) * b ^ i * s (i + 1) := by ring
  have hsup := bounded_quadratic_iteration s hb (mul_nonneg hA hI) hs0 hbound hrec
  intro x hx
  calc
    u x ≤ s 0 := husi 0 x hx
    _ ≤ b * (A * I) := hsup
    _ = b * A * ∫ y in T, u y ∂μ := by dsimp [I]; ring

/-- The multiplication form of the mean-value estimate is equivalent to
its real-integral version whenever volume is finite. -/
theorem meanValue_ennreal_iff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) {u : α → ℝ} {a C : ℝ}
    (hu : IntegrableOn u s μ) (h0 : ∀ x, 0 ≤ u x)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hμs : μ s < ⊤) :
    (ENNReal.ofReal a * μ s ≤ ENNReal.ofReal C *
      ∫⁻ x in s, ENNReal.ofReal (u x) ∂μ) ↔
      a * (μ s).toReal ≤ C * ∫ x in s, u x ∂μ := by
  have hl : ENNReal.ofReal a * μ s = ENNReal.ofReal (a * (μ s).toReal) := by
    rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_toReal hμs.ne]
  have hr : ENNReal.ofReal C * (∫⁻ x in s, ENNReal.ofReal (u x) ∂μ) =
      ENNReal.ofReal (C * ∫ x in s, u x ∂μ) := by
    rw [ENNReal.ofReal_mul hC,
      ofReal_integral_eq_lintegral_ofReal hu (ae_of_all _ h0)]
  rw [hl, hr, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg h0))]

/-- The infinite-integral branch of the exact root needs no finiteness or
division convention. -/
theorem meanValue_ennreal_of_integral_top {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (u : α → ℝ) (a : ℝ) {C : ℝ}
    (hC : 0 < C) (hI : (∫⁻ x in s, ENNReal.ofReal (u x) ∂μ) = ⊤) :
    ENNReal.ofReal a * μ s ≤ ENNReal.ofReal C *
      ∫⁻ x in s, ENNReal.ofReal (u x) ∂μ := by
  rw [hI, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC))]
  exact le_top

/-- The real Euclidean Laplacian is four times the trace of the actual
Wirtinger Levi matrix. For the standard paper metric G=2I this gives the
required positive factor two between the two metric Laplacians. -/
theorem euclidean_laplacian_eq_four_trace_leviC {n : ℕ}
    {f : ComplexVector n → ℝ} {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) :
    Laplacian.laplacian f z = 4 * (Matrix.trace (leviC f z)).re := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (complexVector_realOrthonormalBasis n)]
  simp only [complexVector_realOrthonormalBasis_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, realVec]
  simp only [↓reduceIte, one_smul]
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, leviC, leviMatrix_diag_re hf]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [stdVec]
  ring

/-- The real orthonormal basis already used to identify `lebesgueC` has
exactly the coordinate functionals used by the metric calculator. -/
theorem realBasis_repr {n : ℕ} (v : ComplexVector n) (a : RIdx n) :
    (complexVector_realOrthonormalBasis n).repr v a = realCoord v a := by
  change Complex.orthonormalBasisOneI.repr (v a.1) a.2 = _
  rw [Complex.orthonormalBasisOneI_repr_apply]
  rcases a with ⟨i, a⟩
  fin_cases a <;> rfl

/-- The complex linear map represented by H in the standard complex basis
acts by the actual matrix-vector multiplication. -/
theorem complexMatrix_toLin_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (v : ComplexVector n) (i : Fin n) :
    (Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis H v) i =
      ∑ j, H i j * v j := by
  rw [Matrix.toLin_apply]
  simp [EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, EuclideanSpace.single, Pi.single_apply,
    Matrix.mulVec, dotProduct]

/-- Restriction of the actual complex matrix action to the real basis
produces the realification blocks used by `realMetricFn`. -/
theorem real_toMatrix_complex_toLin {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : RIdx n) :
    LinearMap.toMatrix (complexVector_realOrthonormalBasis n).toBasis
      (complexVector_realOrthonormalBasis n).toBasis
      ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis H).restrictScalars ℝ) a b =
      if a.2 = b.2 then (H a.1 b.1).re
        else if a.2 = 0 then -(H a.1 b.1).im else (H a.1 b.1).im := by
  rw [LinearMap.toMatrix_apply]
  simp only [LinearMap.restrictScalars_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, complexVector_realOrthonormalBasis_apply, realBasis_repr]
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realCoord, complexMatrix_toLin_apply, realVec, EuclideanSpace.single,
      Pi.single_apply, Complex.mul_re, Complex.mul_im]

/-- This identity connects the volume calculator with restriction of
scalars, so its determinant can be evaluated by the field norm theorem. -/
theorem realMetricFn_eq_toMatrix {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    realMetricFn h x z = (2 : ℝ) •
      LinearMap.toMatrix (complexVector_realOrthonormalBasis n).toBasis
        (complexVector_realOrthonormalBasis n).toBasis
        ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (hMat h x z)).restrictScalars ℝ) := by
  ext a b
  simp only [realMetricFn_entries, Matrix.smul_apply, smul_eq_mul,
    real_toMatrix_complex_toLin]

/-- The real determinant has the required square factor in every chart. -/
theorem realMetricFn_det {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    (realMetricFn h x z).det = ((2 : ℝ) ^ n * (hMat h x z).det.re) ^ 2 := by
  rw [realMetricFn_eq_toMatrix, Matrix.det_smul, LinearMap.det_toMatrix,
    LinearMap.det_restrictScalars, LinearMap.det_toLin, Algebra.norm_complex_apply]
  have him : (hMat h x z).det.im = 0 :=
    (Complex.pos_iff.mp (hMat_posDef h x z hz).det_pos).2.symm
  simp only [RIdx, Fintype.card_prod, Fintype.card_fin, Complex.normSq_apply, him,
    mul_zero, add_zero, pow_mul]
  ring

/-- The full project volume-normalization target, proved from its actual
Hermitian metric and real-coordinate definitions. -/
theorem paperVolumeNormalization {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) : PaperVolumeNormalization h := by
  intro x z hz
  rw [realMetricFn_det h x hz, Real.sqrt_sq]
  exact mul_nonneg (by positivity) (hMat_det_re_pos h x hz).le

/-- Real matrix of the actual complex matrix action after restricting its
scalars. This is a concrete linear-algebra construction. -/
def realRepresentation {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  LinearMap.toMatrix (complexVector_realOrthonormalBasis n).toBasis
    (complexVector_realOrthonormalBasis n).toBasis
    ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis H).restrictScalars ℝ)

theorem realRepresentation_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (a b : RIdx n) :
    realRepresentation H a b =
      if a.2 = b.2 then (H a.1 b.1).re
        else if a.2 = 0 then -(H a.1 b.1).im else (H a.1 b.1).im :=
  real_toMatrix_complex_toLin H a b

theorem realRepresentation_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    realRepresentation (A * B) = realRepresentation A * realRepresentation B := by
  unfold realRepresentation
  rw [Matrix.toLin_mul (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis,
    LinearMap.restrictScalars_comp,
    LinearMap.toMatrix_comp (complexVector_realOrthonormalBasis n).toBasis
      (complexVector_realOrthonormalBasis n).toBasis
      (complexVector_realOrthonormalBasis n).toBasis]

theorem realRepresentation_one (n : ℕ) :
    realRepresentation (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold realRepresentation
  rw [Matrix.toLin_one, LinearMap.restrictScalars_id, LinearMap.toMatrix_id]

/-- The actual inverse real metric matrix has the expected inverse complex
matrix blocks and the factor one half. -/
theorem realMetricFn_inverse {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    (realMetricFn h x z)⁻¹ = (1 / 2 : ℝ) • realRepresentation ((hMat h x z)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  have hi : (hMat h x z)⁻¹ * hMat h x z = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (ne_of_gt (hMat_posDef h x z hz).det_pos))
  change ((1 / 2 : ℝ) • realRepresentation ((hMat h x z)⁻¹)) *
    realMetricFn h x z = 1
  rw [realMetricFn_eq_toMatrix]
  change ((1 / 2 : ℝ) • realRepresentation ((hMat h x z)⁻¹)) *
    ((2 : ℝ) • realRepresentation (hMat h x z)) = 1
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← realRepresentation_mul, hi, realRepresentation_one]
  norm_num

/-- Real and imaginary parts of every Levi entry, in terms of the actual
ordinary real Hessian. The two direction indices need not agree. -/
theorem leviMatrix_entry_re_im
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (dir : ι → E) (i j : ι) :
    (leviMatrix f z dir i j).re = (1 / 4 : ℝ) *
      (fderiv ℝ (fderiv ℝ f) z (dir j) (dir i) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • dir j) (Complex.I • dir i)) ∧
    (leviMatrix f z dir i j).im = (1 / 4 : ℝ) *
      (fderiv ℝ (fderiv ℝ f) z (dir j) (Complex.I • dir i) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • dir j) (dir i)) := by
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [leviMatrix, wirt_wirtBar_eq_secondFDeriv hdF]
  simp only [secondFDeriv_ofReal hf]
  constructor <;> simp [Complex.mul_re, Complex.mul_im]

/-- The principal real metric second-order operator is twice the complex
Levi trace, for every Hermitian metric and every C² real chart function.
The vanishing Kähler connection contraction is a separate differential step. -/
theorem principal_realLaplacian_eq_twice_traceWith {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) {f : ComplexVector n → ℝ}
    (hf : ContDiffAt ℝ 2 f z) :
    (∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b *
      fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b)) =
        2 * traceWith (hMat h x z) (leviC f z) := by
  have hre (i j : Fin n) := (leviMatrix_entry_re_im hf stdVec i j).1
  have him (i j : Fin n) := (leviMatrix_entry_re_im hf stdVec i j).2
  rw [realMetricFn_inverse h x hz]
  simp only [Matrix.smul_apply, smul_eq_mul, realRepresentation_apply,
    traceWith, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum,
    Complex.mul_re, leviC, hre, him, Fintype.sum_prod_type, Fin.sum_univ_two, realVec]
  generalize hInv : (hMat h x z)⁻¹ = A
  change Fin n → Fin n → ℂ at A
  norm_num
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [stdVec]
  ring

/-- A multiplier only needs continuity where the test function can be
nonzero; outside its closed support the product is locally zero. -/
theorem continuous_mul_of_continuousAt_tsupport {X : Type*} [TopologicalSpace X]
    {φ u : X → ℝ} (hφ : Continuous φ)
    (hu : ∀ x ∈ tsupport φ, ContinuousAt u x) :
    Continuous (fun x => φ x * u x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.continuousAt.mul (hu x hx)
  · have heq : (fun y => φ y * u y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact continuousAt_const.congr heq.symm

/-- Compactly supported test products in a chart are genuinely integrable,
even if the second factor is only continuous on that chart. -/
theorem integrable_compactTest_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsLocallyFiniteMeasure μ]
    {O : Set E} (hO : IsOpen O) {φ u : E → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ O)
    (hu : ContinuousOn u O) : Integrable (fun x => φ x * u x) μ := by
  have hc : Continuous (fun x => φ x * u x) :=
    continuous_mul_of_continuousAt_tsupport hφ fun x hx =>
      hu.continuousAt (hO.mem_nhds (hφO hx))
  exact hc.integrable_of_hasCompactSupport hcφ.mul_right

/-- Scalar integration by parts for an actual compact test function in an
open coordinate domain. All product integrability is proved internally. -/
theorem integral_compactTest_direction_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {O : Set E} (hO : IsOpen O) {φ u : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ O)
    (hu : ContDiffOn ℝ 1 u O) (v : E) :
    ∫ x, φ x * fderiv ℝ u x v ∂μ =
      -(∫ x, fderiv ℝ φ x v * u x ∂μ) := by
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdφO : tsupport (fun x => fderiv ℝ φ x v) ⊆ O :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφO
  have hdu : ContinuousOn (fun x => fderiv ℝ u x v) O :=
    (hu.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_compactTest_mul μ hO hdφ (hcφ.fderiv_apply ℝ v) hdφO hu.continuousOn)
    (integrable_compactTest_mul μ hO hφ.continuous hcφ hφO hdu)
    (integrable_compactTest_mul μ hO hφ.continuous hcφ hφO hu.continuousOn)
    (fun x _ => hφ.differentiable one_ne_zero x)
    (fun x hx => (hu.contDiffAt (hO.mem_nhds (hφO hx))).differentiableAt one_ne_zero)

/-- The coordinate divergence identity for a finite family of genuine C¹
fluxes and a compactly supported test function. -/
theorem integral_compactTest_divergence_on
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {O : Set E} (hO : IsOpen O) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ O)
    (F : ι → E → ℝ) (hF : ∀ i, ContDiffOn ℝ 1 (F i) O) (v : ι → E) :
    ∫ x, φ x * (∑ i, fderiv ℝ (F i) x (v i)) ∂μ =
      -(∫ x, ∑ i, fderiv ℝ φ x (v i) * F i x ∂μ) := by
  have hL (i : ι) : Integrable (fun x => φ x * fderiv ℝ (F i) x (v i)) μ :=
    integrable_compactTest_mul μ hO hφ.continuous hcφ hφO
      (((hF i).continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const)
  have hR (i : ι) : Integrable (fun x => fderiv ℝ φ x (v i) * F i x) μ :=
    integrable_compactTest_mul μ hO
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hcφ.fderiv_apply ℝ (v i)) ((tsupport_fderiv_apply_subset ℝ (v i)).trans hφO)
      (hF i).continuousOn
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hL i),
    integral_finsetSum Finset.univ (fun i _ => hR i)]
  simp_rw [integral_compactTest_direction_on μ hO hφ hcφ hφO (hF _) (v _)]
  exact Finset.sum_neg_distrib _

/-- The nested coordinate derivative used by the real Laplacian is the
ordinary Hessian entry whenever the chart scalar is C². -/
theorem rDeriv_rDeriv_eq_hessian {n : ℕ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) (a b : RIdx n) :
    rDeriv (fun w => rDeriv f w b) z a =
      fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold rDeriv
  rw [fderiv_clm_apply hdf (differentiableAt_const (realVec b))]
  simp

/-- Entrywise smoothness of matrix inversion, proved using the actual
adjugate/determinant formula rather than an assumed inverse-metric field. -/
theorem contDiffOn_matrix_inv {E ι 𝕜 : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    {A : E → Matrix ι ι 𝕜} {s : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) s)
    (hdet : ∀ z ∈ s, (A z).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ ∞ (fun z => (A z)⁻¹ i j) s :=
  SharedCalculus.contDiffOn_matrix_inv hA hdet i j

theorem hMat_inverse_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => (hMat g.form x z)⁻¹ i j) (chartTarget x) :=
  contDiffOn_matrix_inv (hMat_contDiffOn g x)
    (fun z hz => ne_of_gt (hMat_posDef g.form x z hz).det_pos) i j

/-- The inverse real metric coefficients are smooth on each actual chart. -/
theorem realMetricFn_inverse_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => (realMetricFn g.form x z)⁻¹ a b) (chartTarget x) := by
  apply contDiffOn_matrix_inv (metricSmooth_of_smoothMetric g x)
  intro z hz
  rw [realMetricFn_det g.form x hz]
  exact pow_ne_zero _ (mul_ne_zero (by norm_num) (ne_of_gt (hMat_det_re_pos g.form x hz)))

/-- The already proved determinant factor gives full smoothness of the
volume density, including its positive square-root branch. -/
theorem volumeDensity_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => Real.sqrt (realMetricFn g.form x z).det) (chartTarget x) := by
  have hd : ContDiffOn ℝ ∞ (fun z => (hMat g.form x z).det.re) (chartTarget x) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (contDiffOn_matrix_det (hMat_contDiffOn g x))
  exact (contDiffOn_const.mul hd).congr fun z hz => paperVolumeNormalization g.form x z hz

theorem rDeriv_contDiffOn {n : ℕ} {f : ComplexVector n → ℝ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (a : RIdx n) : ContDiffOn ℝ ∞ (fun z => rDeriv f z a) O :=
  (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

/-- The genuine scalar metric flux in a fixed real chart, including the
actual Riemannian volume density. -/
def scalarMetricFlux {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (u : M.Carrier → ℝ)
    (a : RIdx n) (z : ComplexVector n) : ℝ :=
  Real.sqrt (realMetricFn h x z).det *
    ∑ b, (realMetricFn h x z)⁻¹ a b * rDeriv (inChart x u) z b

theorem scalarMetricFlux_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) (a : RIdx n) :
    ContDiffOn ℝ ∞ (scalarMetricFlux g.form x u a) (chartTarget x) := by
  apply (volumeDensity_contDiffOn g x).mul
  apply ContDiffOn.sum
  intro b _
  exact (realMetricFn_inverse_contDiffOn g x a b).mul
    (rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x) (hu x) b)

/-- Integration by parts for the computed scalar Riemannian flux, on every
actual chart, with all coefficient regularity and integrability discharged. -/
theorem integral_scalarMetricFlux {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * (∑ a, rDeriv (scalarMetricFlux g.form x u a) z a) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * scalarMetricFlux g.form x u a z ∂lebesgueC n) := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  exact integral_compactTest_divergence_on (lebesgueC n)
    (isOpen_extChartAt_target (I := ComplexModel n) x) hφ hcφ hφO
    (scalarMetricFlux g.form x u)
    (fun a => (scalarMetricFlux_contDiffOn g hu x a).of_le (by simp)) realVec

/-- The signed permutation representing multiplication by i on the fixed
real coordinate basis. -/
def jIndex (n : ℕ) : RIdx n ≃ RIdx n :=
  Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.swap (0 : Fin 2) 1)

def jSign {n : ℕ} (a : RIdx n) : ℝ := if a.2 = 0 then 1 else -1

theorem jIndex_involutive {n : ℕ} (a : RIdx n) : jIndex n (jIndex n a) = a := by
  rcases a with ⟨i, a⟩
  fin_cases a <;> simp [jIndex]

theorem jSign_jIndex {n : ℕ} (a : RIdx n) : jSign (jIndex n a) = -jSign a := by
  rcases a with ⟨i, a⟩
  fin_cases a <;> simp [jIndex, jSign]

theorem jSign_sq {n : ℕ} (a : RIdx n) : jSign a * jSign a = 1 := by
  simp only [jSign]
  split_ifs <;> norm_num

theorem kahlerFormFn_entries {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z a b = 2 *
      (if a.2 = b.2 then (hMat h x z a.1 b.1).im
        else if a.2 = 0 then (hMat h x z a.1 b.1).re
        else -(hMat h x z a.1 b.1).re) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [kahlerFormFn, realVec, hMat, stdVec, chartVec_smul,
      HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right]

theorem realMetricFn_jIndex {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    realMetricFn h x z (jIndex n a) (jIndex n b) =
      jSign a * jSign b * realMetricFn h x z a b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [jIndex, jSign, realMetricFn_entries]

theorem kahlerFormFn_jIndex_left {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z (jIndex n a) b = -jSign a * realMetricFn h x z a b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [jIndex, jSign, realMetricFn_entries, kahlerFormFn_entries]

theorem kahlerFormFn_jIndex_right {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z a (jIndex n b) = jSign b * realMetricFn h x z a b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [jIndex, jSign, realMetricFn_entries, kahlerFormFn_entries]

theorem kahlerFormFn_eq_jIndex_metric {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn h x z a b = jSign a * realMetricFn h x z (jIndex n a) b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [jIndex, jSign, realMetricFn_entries, kahlerFormFn_entries]

theorem realMetricFn_isSymm {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (realMetricFn h x z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  unfold realMetricFn
  rw [(h (chartInv x z)).conjugate_symmetric]
  simp

theorem realMetricFn_inverse_jIndex {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    (realMetricFn h x z)⁻¹ (jIndex n a) (jIndex n b) =
      jSign a * jSign b * (realMetricFn h x z)⁻¹ a b := by
  rw [realMetricFn_inverse h x hz]
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.smul_apply, smul_eq_mul, realRepresentation_apply, jIndex, jSign]

theorem realMetricFn_differentiableAt {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    DifferentiableAt ℝ (fun w => realMetricFn g.form x w a b) z :=
  ((metricSmooth_of_smoothMetric g x a b).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt
      (by simp)

theorem rDeriv_const_mul {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (c : ℝ) (a : RIdx n) :
    rDeriv (fun w => c * f w) z a = c * rDeriv f z a := by
  unfold rDeriv
  rw [fderiv_const_mul hf c]
  simp

theorem rDeriv_realMetricFn_jIndex {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun w => realMetricFn g.form x w (jIndex n b) (jIndex n c)) z a =
      jSign b * jSign c * rDeriv (fun w => realMetricFn g.form x w b c) z a := by
  have heq : (fun w => realMetricFn g.form x w (jIndex n b) (jIndex n c)) =
      (fun w => (jSign b * jSign c) * realMetricFn g.form x w b c) := by
    funext w
    exact realMetricFn_jIndex g.form x w b c
  rw [heq]
  exact rDeriv_const_mul (realMetricFn_differentiableAt g x hz b c) _ a

theorem rDeriv_realMetricFn_symm {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b c : RIdx n) :
    rDeriv (fun w => realMetricFn h x w b c) z a =
      rDeriv (fun w => realMetricFn h x w c b) z a := by
  have heq : (fun w => realMetricFn h x w b c) =
      (fun w => realMetricFn h x w c b) := by
    funext w
    exact (realMetricFn_isSymm h x w).apply c b
  rw [heq]

/-- The actual closed-Kähler-form equation, with a signed J-coordinate
inserted, yields the derivative identity used in harmonic coordinates. -/
theorem kahler_metric_derivative_identity {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) (a b d : RIdx n) :
    -rDeriv (fun w => realMetricFn g.form x w b d) (chartPt x x) a +
      jSign b * jSign d * rDeriv
        (fun w => realMetricFn g.form x w (jIndex n d) a) (chartPt x x) (jIndex n b) +
      rDeriv (fun w => realMetricFn g.form x w a b) (chartPt x x) d = 0 := by
  have hk := hK x a (jIndex n b) d
  have h1 : (fun w => kahlerFormFn g.form x w (jIndex n b) d) =
      (fun w => (-jSign b) * realMetricFn g.form x w b d) := by
    funext w
    exact kahlerFormFn_jIndex_left g.form x w b d
  have h2 : (fun w => kahlerFormFn g.form x w d a) =
      (fun w => jSign d * realMetricFn g.form x w (jIndex n d) a) := by
    funext w
    exact kahlerFormFn_eq_jIndex_metric g.form x w d a
  have h3 : (fun w => kahlerFormFn g.form x w a (jIndex n b)) =
      (fun w => jSign b * realMetricFn g.form x w a b) := by
    funext w
    exact kahlerFormFn_jIndex_right g.form x w a b
  change rDeriv _ (chartPt x x) a + rDeriv _ (chartPt x x) (jIndex n b) +
    rDeriv _ (chartPt x x) d = 0 at hk
  have hG (p q : RIdx n) :
      DifferentiableAt ℝ (fun w => realMetricFn g.form x w p q) (chartPt x x) :=
    realMetricFn_differentiableAt g x (mem_extChartAt_target x) p q
  rw [h1, h2, h3,
    rDeriv_const_mul (hG b d) (-jSign b) a,
    rDeriv_const_mul (hG (jIndex n d) a) (jSign d) (jIndex n b),
    rDeriv_const_mul (hG a b) (jSign b) d] at hk
  by_cases hb : b.2 = 0
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith

/-- Applying J to both summation indices is an actual permutation of the
finite real basis. -/
theorem sum_jIndex_two {n : ℕ} (F : RIdx n → RIdx n → ℝ) :
    (∑ a, ∑ b, F (jIndex n a) (jIndex n b)) = ∑ a, ∑ b, F a b := by
  simp only [Equiv.sum_comp]
  exact (jIndex n).sum_comp fun a => ∑ b, F a b

/-- Contraction of the actual Kähler derivative identity with the actual
inverse metric. This is the cancellation underlying harmonic holomorphic
coordinates; no connection or Laplacian identity is assumed. -/
theorem kahler_metric_derivative_trace {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) (d : RIdx n) :
    2 * (∑ a, ∑ b, (realMetricFn g.form x (chartPt x x))⁻¹ a b *
      rDeriv (fun w => realMetricFn g.form x w b d) (chartPt x x) a) =
      ∑ a, ∑ b, (realMetricFn g.form x (chartPt x x))⁻¹ a b *
        rDeriv (fun w => realMetricFn g.form x w a b) (chartPt x x) d := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form x (chartPt x x))⁻¹
  let D : RIdx n → RIdx n → RIdx n → ℝ := fun a b c =>
    rDeriv (fun w => realMetricFn g.form x w b c) (chartPt x x) a
  have hJA (a b : RIdx n) : A (jIndex n a) (jIndex n b) = jSign a * jSign b * A a b := by
    simpa only [A, chartPt] using
      realMetricFn_inverse_jIndex g.form x (mem_extChartAt_target x) a b
  have hJD (a b c : RIdx n) : D a (jIndex n b) (jIndex n c) = jSign b * jSign c * D a b c :=
    rDeriv_realMetricFn_jIndex g x (mem_extChartAt_target x) a b c
  have hSA (a b : RIdx n) : A b a = A a b := by
    simpa only [A] using (realMetricFn_isSymm g.form x (chartPt x x)).inv.apply a b
  have hSD (a b c : RIdx n) : D a b c = D a c b :=
    rDeriv_realMetricFn_symm g.form x (chartPt x x) a b c
  let T := ∑ a, ∑ b, A a b * D a b d
  let U := ∑ a, ∑ b, A a b * jSign b * jSign d * D (jIndex n b) (jIndex n d) a
  let S := ∑ a, ∑ b, A a b * D d a b
  have hU : U = -T := by
    have hterm (a b : RIdx n) :
        A (jIndex n a) (jIndex n b) * jSign (jIndex n b) * jSign d *
          D (jIndex n (jIndex n b)) (jIndex n d) (jIndex n a) = -A a b * D b d a := by
      rw [hJA, jSign_jIndex, jIndex_involutive, hJD]
      calc
        _ = -(jSign a * jSign a) * (jSign b * jSign b) * (jSign d * jSign d) *
            (A a b * D b d a) := by ring
        _ = -A a b * D b d a := by rw [jSign_sq, jSign_sq, jSign_sq]; ring
    calc
      U = ∑ a, ∑ b, A (jIndex n a) (jIndex n b) * jSign (jIndex n b) * jSign d *
          D (jIndex n (jIndex n b)) (jIndex n d) (jIndex n a) :=
        (sum_jIndex_two (fun a b => A a b * jSign b * jSign d *
          D (jIndex n b) (jIndex n d) a)).symm
      _ = ∑ a, ∑ b, -A a b * D b d a := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact hterm a b
      _ = -(∑ a, ∑ b, A a b * D b d a) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
      _ = -T := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hSA, hSD]
  have hsum : -T + U + S = 0 := by
    have hzero : (∑ a, ∑ b, A a b *
        (-D a b d + jSign b * jSign d * D (jIndex n b) (jIndex n d) a + D d a b)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      rw [show -D a b d + jSign b * jSign d * D (jIndex n b) (jIndex n d) a + D d a b = 0 from
        kahler_metric_derivative_identity g hK x a b d]
      exact mul_zero _
    simpa only [T, U, S, mul_add, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, mul_assoc] using hzero
  have hfinal : 2 * T = S := by linarith
  simpa only [T, S, A, D] using hfinal

theorem sum_three_cycle {n : ℕ} (F : RIdx n → RIdx n → RIdx n → ℝ) :
    (∑ a, ∑ b, ∑ d, F a b d) = ∑ d, ∑ a, ∑ b, F a b d := by
  calc
    (∑ a, ∑ b, ∑ d, F a b d) = ∑ a, ∑ d, ∑ b, F a b d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, F a b d := Finset.sum_comm

/-- The trace of the actual Levi--Civita Christoffel symbols vanishes in
the complex chart of a Kähler metric. -/
theorem kahler_christoffel_trace {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) (c : RIdx n) :
    (∑ a, ∑ b, (realMetricFn g.form x (chartPt x x))⁻¹ a b *
      christoffel g.form x (chartPt x x) c a b) = 0 := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form x (chartPt x x))⁻¹
  let D : RIdx n → RIdx n → RIdx n → ℝ := fun a b d =>
    rDeriv (fun w => realMetricFn g.form x w b d) (chartPt x x) a
  have hSA (a b : RIdx n) : A b a = A a b :=
    (realMetricFn_isSymm g.form x (chartPt x x)).inv.apply a b
  have hzero (d : RIdx n) : (∑ a, ∑ b, A a b * (D a b d + D b a d - D d a b)) = 0 := by
    have hT : 2 * (∑ a, ∑ b, A a b * D a b d) = ∑ a, ∑ b, A a b * D d a b :=
      kahler_metric_derivative_trace g hK x d
    have hswap : (∑ a, ∑ b, A a b * D b a d) = ∑ a, ∑ b, A a b * D a b d := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hSA]
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hswap]
    linarith
  change (∑ a, ∑ b, A a b * ((1 / 2 : ℝ) *
    ∑ d, A c d * (D a b d + D b a d - D d a b))) = 0
  simp only [Finset.mul_sum]
  rw [sum_three_cycle]
  calc
    (∑ d, ∑ a, ∑ b, A a b * ((1 / 2 : ℝ) * (A c d *
        (D a b d + D b a d - D d a b)))) =
        ∑ d, ((1 / 2 : ℝ) * A c d) *
          (∑ a, ∑ b, A a b * (D a b d + D b a d - D d a b)) := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = 0 := by simp only [hzero, mul_zero, Finset.sum_const_zero]

/-- The independently defined real Levi--Civita scalar Laplacian calculator
at each manifold point is twice the paper's complex Laplacian. -/
theorem kahler_realLaplacian_center {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (x : M.Carrier) :
    (∑ a, ∑ b, (realMetricFn g.form x (chartPt x x))⁻¹ a b *
      (rDeriv (fun w => rDeriv (inChart x u) w b) (chartPt x x) a -
        ∑ c, christoffel g.form x (chartPt x x) c a b *
          rDeriv (inChart x u) (chartPt x x) c)) = 2 * laplacian g.form u x := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form x (chartPt x x))⁻¹
  have hf : ContDiffAt ℝ 2 (inChart x u) (chartPt x x) :=
    (contDiffAt_inChart hu x (mem_extChartAt_target x)).of_le (by simp)
  have hp : (∑ a, ∑ b, A a b *
      rDeriv (fun w => rDeriv (inChart x u) w b) (chartPt x x) a) =
      2 * laplacian g.form u x := by
    simp only [rDeriv_rDeriv_eq_hessian hf]
    exact principal_realLaplacian_eq_twice_traceWith g.form x (mem_extChartAt_target x) hf
  have hc : (∑ a, ∑ b, A a b *
      (∑ c, christoffel g.form x (chartPt x x) c a b *
        rDeriv (inChart x u) (chartPt x x) c)) = 0 := by
    simp only [Finset.mul_sum]
    rw [sum_three_cycle]
    apply Finset.sum_eq_zero
    intro c _
    calc
      (∑ a, ∑ b, A a b * (christoffel g.form x (chartPt x x) c a b *
          rDeriv (inChart x u) (chartPt x x) c)) =
          (∑ a, ∑ b, A a b * christoffel g.form x (chartPt x x) c a b) *
            rDeriv (inChart x u) (chartPt x x) c := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = 0 := by rw [show (∑ a, ∑ b, A a b * christoffel g.form x (chartPt x x) c a b) = 0 from
        kahler_christoffel_trace g hK x c]; exact zero_mul _
  change (∑ a, ∑ b, A a b * _) = _
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hc, sub_zero, hp]

/-- Differentiate the genuine determinant as a continuous alternating
function of its rows. -/
theorem fderiv_matrix_det_sum_updateRow
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z) (v : E) :
    fderiv ℝ (fun w => (A w).det) z v =
      ∑ i, ((A z).updateRow i (fderiv ℝ (fun w => A w i) z v)).det := by
  let detAlt : (ι → ℝ) [⋀^ι]→L[ℝ] ℝ :=
    { Matrix.detRowAlternating with cont := continuous_id.matrix_det }
  have hrow (i : ι) : DifferentiableAt ℝ (fun w => A w i) z :=
    differentiableAt_pi.mpr (hA i)
  have h := fderiv_continuousAlternatingMap_apply_apply
    (f := fun _ : E => detAlt) (g := fun i w => A w i)
    (differentiableAt_const detAlt) hrow v
  have hfun : (fun w : E => detAlt (fun i => A w i)) = (fun w => (A w).det) := by rfl
  have hupdate (i : ι) :
      detAlt (Function.update (fun j => A z j) i (fderiv ℝ (fun w => A w i) z v)) =
        ((A z).updateRow i (fderiv ℝ (fun w => A w i) z v)).det := by rfl
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply,
    ContinuousAlternatingMap.coe_zero, zero_add] at h
  rw [hfun] at h
  simpa only [hupdate] using h

/-- A replaced row can be expressed in the original invertible row basis;
its determinant is the corresponding inverse-matrix coordinate. -/
theorem det_updateRow_eq_det_mul_inverse_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) (i : ι) (row : ι → ℝ) :
    (A.updateRow i row).det = A.det * (row ᵥ* A⁻¹) i := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hc : (row ᵥ* A⁻¹) ᵥ* A = row := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hunit, Matrix.vecMul_one]
  have hrow : (∑ k, (row ᵥ* A⁻¹) k • A k) = row := by
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] using
      congrFun hc j
  nth_rw 1 [← hrow]
  rw [Matrix.det_updateRow_sum]
  simp only [smul_eq_mul, mul_comm]

/-- Jacobi's determinant derivative formula for the actual real matrix
field, with the row derivatives kept as ordinary Fréchet derivatives. -/
theorem fderiv_matrix_det_trace
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    fderiv ℝ (fun w => (A w).det) z v = (A z).det *
      Matrix.trace ((A z)⁻¹ * (Matrix.of fun i j => fderiv ℝ (fun w => A w i) z v j)) := by
  rw [fderiv_matrix_det_sum_updateRow hA]
  simp_rw [det_updateRow_eq_det_mul_inverse_coordinate (A z) hdet]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Matrix.vecMul, dotProduct, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem fderiv_matrix_mul_entry
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A B : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z)
    (v : E) (i j : ι) :
    fderiv ℝ (fun w => (A w * B w) i j) z v =
      ∑ k, (fderiv ℝ (fun w => A w i k) z v * B z k j +
        A z i k * fderiv ℝ (fun w => B w k j) z v) := by
  simp only [Matrix.mul_apply]
  have hprod (k : ι) : DifferentiableAt ℝ (fun w => A w i k * B w k j) z :=
    (hA i k).mul (hB k j)
  rw [fderiv_fun_sum (fun k _ => hprod k)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_mul (hA i k) (hB k j)]
  simp <;> ring

/-- The true inverse-matrix derivative on an open domain where the actual
matrix determinant does not vanish. -/
theorem fderiv_matrix_inv_entry
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ} {O : Set E}
    (hO : IsOpen O) (hA : ∀ i j, ContDiffOn ℝ ∞ (fun w => A w i j) O)
    (hdet : ∀ w ∈ O, (A w).det ≠ 0) {z : E} (hz : z ∈ O)
    (v : E) (i j : ι) :
    fderiv ℝ (fun w => (A w)⁻¹ i j) z v =
      -(((A z)⁻¹ * (Matrix.of fun p q => fderiv ℝ (fun w => A w p q) z v) * (A z)⁻¹) i j) := by
  let DA : Matrix ι ι ℝ := Matrix.of fun p q => fderiv ℝ (fun w => A w p q) z v
  let DI : Matrix ι ι ℝ := Matrix.of fun p q => fderiv ℝ (fun w => (A w)⁻¹ p q) z v
  have hAd (p q : ι) : DifferentiableAt ℝ (fun w => A w p q) z :=
    ((hA p q).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hId (p q : ι) : DifferentiableAt ℝ (fun w => (A w)⁻¹ p q) z :=
    ((contDiffOn_matrix_inv hA hdet p q).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdprod (p q : ι) : fderiv ℝ (fun w => ((A w)⁻¹ * A w) p q) z v = 0 := by
    have heq : (fun w => ((A w)⁻¹ * A w) p q) =ᶠ[𝓝 z]
        (fun _ : E => (1 : Matrix ι ι ℝ) p q) := by
      filter_upwards [hO.mem_nhds hz] with w hw
      exact congrArg (fun M : Matrix ι ι ℝ => M p q)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet w hw)))
    rw [heq.fderiv_eq]
    simp
  have hm : DI * A z + (A z)⁻¹ * DA = 0 := by
    ext p q
    have hpq := hdprod p q
    rw [fderiv_matrix_mul_entry hId hAd] at hpq
    simpa only [DA, DI, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.zero_apply, Finset.sum_add_distrib] using hpq
  have hm' := congrArg (fun M : Matrix ι ι ℝ => M * (A z)⁻¹) hm
  have hDI : DI = -((A z)⁻¹ * DA * (A z)⁻¹) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [Matrix.add_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet z hz)),
      Matrix.mul_one, Matrix.zero_mul] using hm'
  have hentry := congrArg (fun M : Matrix ι ι ℝ => M i j) hDI
  simpa only [DI, DA, Matrix.of_apply, Matrix.neg_apply] using hentry

theorem fderiv_matrix_row_apply
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (v : E) (i j : ι) :
    fderiv ℝ (fun w => A w i) z v j = fderiv ℝ (fun w => A w i j) z v := by
  have hrow : DifferentiableAt ℝ (fun w => A w i) z := differentiableAt_pi.mpr (hA i)
  rw [fderiv_apply hrow j]
  simp

/-- The derivative of the actual volume density, with its coefficient
computed by Jacobi's formula and the positive square-root identity. -/
theorem fderiv_volumeDensity {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    fderiv ℝ (fun w => Real.sqrt (realMetricFn g.form x w).det) z v =
      (Real.sqrt (realMetricFn g.form x z).det / 2) *
        Matrix.trace ((realMetricFn g.form x z)⁻¹ *
          (Matrix.of fun a b => fderiv ℝ (fun w => realMetricFn g.form x w a b) z v)) := by
  have hGd (a b : RIdx n) :
      DifferentiableAt ℝ (fun w => realMetricFn g.form x w a b) z :=
    realMetricFn_differentiableAt g x hz a b
  have hdetd : DifferentiableAt ℝ (fun w => (realMetricFn g.form x w).det) z :=
    ((contDiffOn_matrix_det (metricSmooth_of_smoothMetric g x)).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hρ : 0 < Real.sqrt (realMetricFn g.form x z).det := by
    rw [paperVolumeNormalization g.form x z hz]
    exact mul_pos (by positivity) (hMat_det_re_pos g.form x hz)
  have hdet : 0 < (realMetricFn g.form x z).det := by
    rw [realMetricFn_det g.form x hz]
    exact sq_pos_of_pos (mul_pos (by positivity) (hMat_det_re_pos g.form x hz))
  rw [fderiv_sqrt hdetd (ne_of_gt hdet)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_matrix_det_trace hGd (ne_of_gt hdet)]
  simp_rw [fderiv_matrix_row_apply hGd]
  have hc : (1 / (2 * Real.sqrt (realMetricFn g.form x z).det)) *
      (realMetricFn g.form x z).det = Real.sqrt (realMetricFn g.form x z).det / 2 := by
    field_simp
    nlinarith [Real.sq_sqrt hdet.le]
  rw [← mul_assoc, hc]

/-- Smooth local multipliers extend by the locally zero test factor. -/
theorem contDiff_mul_of_contDiffAt_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ u : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hu : ∀ x ∈ tsupport φ, ContDiffAt ℝ ∞ u x) :
    ContDiff ℝ ∞ (fun x => φ x * u x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.mul (hu x hx)
  · have heq : (fun y => φ y * u y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

section ChartVolume

variable {n : ℕ} {M : ComplexManifold n}

/- These five elementary chart-volume proofs are reused, with authorization,
from the independently compiled L07 chart-volume snippet. Keeping them here
avoids any dependency of scalar geometry on the bundle-solvability module. -/
theorem chartInv_chartPt_of_mem (a x : M.Carrier)
    (hx : x ∈ (chartAt (ComplexVector n) a).source) :
    chartInv a (chartPt a x) = x := by
  apply (extChartAt (ComplexModel n) a).left_inv
  simpa only [extChartAt_source] using hx

def chartInvExtension (a : M.Carrier) (z : ComplexVector n) : M.Carrier :=
  @ite _ (z ∈ chartTarget a) (Classical.propDecidable _) (chartInv a z) a

theorem chartInvExtension_measurable (a : M.Carrier) :
    Measurable (chartInvExtension a) := by
  classical
  change Measurable ((chartTarget a).piecewise (chartInv a) (fun _ => a))
  exact (continuousOn_extChartAt_symm (I := ComplexModel n) a).measurable_piecewise
    (continuousOn_const (c := a)) (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet

theorem chart_image_eq_extension_preimage (a : M.Carrier) (s : Set M.Carrier) :
    chartPt a '' (s ∩ (extChartAt (ComplexModel n) a).source) =
      chartInvExtension a ⁻¹' s ∩ chartTarget a := by
  ext z
  constructor
  · rintro ⟨y, ⟨hys, hy⟩, rfl⟩
    have hz : chartPt a y ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source hy
    refine ⟨?_, hz⟩
    simpa only [Set.mem_preimage, chartInvExtension, if_pos hz,
      chartInv_chartPt_of_mem a y (by simpa only [extChartAt_source] using hy)] using hys
  · rintro ⟨hzs, hz⟩
    refine ⟨chartInv a z, ⟨?_, (extChartAt (ComplexModel n) a).map_target hz⟩, ?_⟩
    · simpa only [Set.mem_preimage, chartInvExtension, if_pos hz] using hzs
    · exact (extChartAt (ComplexModel n) a).right_inv hz

theorem riemannianVolume_restrict_eq_map (h : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume h μ) (a : M.Carrier) :
    μ.restrict (extChartAt (ComplexModel n) a).source =
      Measure.map (chartInvExtension a)
        (((lebesgueC n).restrict (chartTarget a)).withDensity
          (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn h a z).det))) := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, Measure.map_apply (chartInvExtension_measurable a) hs,
    withDensity_apply _ ((chartInvExtension_measurable a) hs), Measure.restrict_restrict]
  · rw [hμ a (s ∩ (extChartAt (ComplexModel n) a).source)
      (hs.inter (isOpen_extChartAt_source (I := ComplexModel n) a).measurableSet)
      (by simpa only [extChartAt_source] using (Set.inter_subset_right :
        s ∩ (extChartAt (ComplexModel n) a).source ⊆ (extChartAt (ComplexModel n) a).source)),
      chart_image_eq_extension_preimage]
  · exact (chartInvExtension_measurable a) hs

/-- Exact scalar Lebesgue-integral transport for the root's actual volume
measure, with its computed density and inverse chart. -/
theorem lintegral_chart_volume (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier)
    (f : M.Carrier → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in (extChartAt (ComplexModel n) a).source, f y ∂μ =
      ∫⁻ z in chartTarget a, ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det) *
        f (chartInv a z) ∂lebesgueC n := by
  have ht : MeasurableSet (chartTarget a) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det))
      ((lebesgueC n).restrict (chartTarget a)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((volumeDensity_continuousOn g a).aemeasurable ht)
  have hfg : AEMeasurable (fun z => f (chartInvExtension a z))
      ((lebesgueC n).restrict (chartTarget a)) :=
    (hf.comp (chartInvExtension_measurable a)).aemeasurable
  rw [riemannianVolume_restrict_eq_map g.form μ hμ a,
    lintegral_map hf (chartInvExtension_measurable a),
    lintegral_withDensity_eq_lintegral_mul₀ hd hfg]
  apply setLIntegral_congr_fun ht
  intro z hz
  simp only [Pi.mul_apply, chartInvExtension, if_pos hz]

/-- Exact real scalar integral transport, including the actual density.
No integrability hypothesis is needed for equality of the Bochner integrals. -/
theorem integral_chart_volume (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier)
    (f : M.Carrier → ℝ) (hf : Measurable f) :
    ∫ y in (extChartAt (ComplexModel n) a).source, f y ∂μ =
      ∫ z in chartTarget a, Real.sqrt (realMetricFn g.form a z).det *
        f (chartInv a z) ∂lebesgueC n := by
  have ht : MeasurableSet (chartTarget a) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det))
      ((lebesgueC n).restrict (chartTarget a)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((volumeDensity_continuousOn g a).aemeasurable ht)
  rw [riemannianVolume_restrict_eq_map g.form μ hμ a,
    integral_map (chartInvExtension_measurable a).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hd
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun ht
  intro z hz
  simp only [chartInvExtension, if_pos hz, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]

end ChartVolume

/-- The derivative of the computed density times inverse-metric entry.
Both matrix derivative formulas on the right have been proved above. -/
theorem rDeriv_density_inverse_entry {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun w => Real.sqrt (realMetricFn g.form x w).det *
      (realMetricFn g.form x w)⁻¹ a b) z c =
      (Real.sqrt (realMetricFn g.form x z).det / 2) *
        Matrix.trace ((realMetricFn g.form x z)⁻¹ *
          (Matrix.of fun p q => rDeriv (fun w => realMetricFn g.form x w p q) z c)) *
            (realMetricFn g.form x z)⁻¹ a b -
      Real.sqrt (realMetricFn g.form x z).det *
        (((realMetricFn g.form x z)⁻¹ *
          (Matrix.of fun p q => rDeriv (fun w => realMetricFn g.form x w p q) z c) *
            (realMetricFn g.form x z)⁻¹) a b) := by
  have hρd : DifferentiableAt ℝ (fun w => Real.sqrt (realMetricFn g.form x w).det) z :=
    ((volumeDensity_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hId : DifferentiableAt ℝ (fun w => (realMetricFn g.form x w)⁻¹ a b) z :=
    ((realMetricFn_inverse_contDiffOn g x a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hdet : ∀ w ∈ chartTarget x, (realMetricFn g.form x w).det ≠ 0 := by
    intro w hw
    rw [realMetricFn_det g.form x hw]
    exact pow_ne_zero _ (mul_ne_zero (by norm_num) (ne_of_gt (hMat_det_re_pos g.form x hw)))
  unfold rDeriv
  rw [fderiv_fun_mul hρd hId]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_volumeDensity g x hz,
    fderiv_matrix_inv_entry (isOpen_extChartAt_target (I := ComplexModel n) x)
      (metricSmooth_of_smoothMetric g x) hdet hz]
  ring

/-- Finite matrix algebra collecting the two derivative contributions to
a density-weighted inverse-metric column. -/
theorem sum_density_inverse_derivative_form
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (D : ι → Matrix ι ι ℝ) (ρ : ℝ) (b : ι) :
    (∑ a : ι, ((ρ / 2) * Matrix.trace (A * D a) * A a b - ρ * ((A * D a * A) a b))) =
      (ρ / 2) * (∑ a : ι, A a b * Matrix.trace (A * D a)) -
        ρ * (∑ q : ι, A q b * (∑ a : ι, ∑ p : ι, A a p * D a p q)) := by
  have hfirst : (∑ a : ι, (ρ / 2) * Matrix.trace (A * D a) * A a b) =
      (ρ / 2) * (∑ a : ι, A a b * Matrix.trace (A * D a)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hsecond : (∑ a : ι, ρ * ((A * D a * A) a b)) =
      ρ * (∑ q : ι, A q b * (∑ a : ι, ∑ p : ι, A a p * D a p q)) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [Finset.sum_sub_distrib, hfirst, hsecond]

/-- The actual volume-weighted inverse metric has zero coordinate-column
 divergence at the center of each Kähler chart. -/
theorem kahler_density_inverse_divergence_center {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) (b : RIdx n) :
    (∑ a, rDeriv (fun w => Real.sqrt (realMetricFn g.form x w).det *
      (realMetricFn g.form x w)⁻¹ a b) (chartPt x x) a) = 0 := by
  let z := chartPt x x
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form x z)⁻¹
  let D : RIdx n → Matrix (RIdx n) (RIdx n) ℝ := fun c =>
    Matrix.of fun p q => rDeriv (fun w => realMetricFn g.form x w p q) z c
  let ρ := Real.sqrt (realMetricFn g.form x z).det
  let T : RIdx n → ℝ := fun c => ∑ a, ∑ p, A a p * D a p c
  have hD (c p q : RIdx n) : D c p q = D c q p :=
    rDeriv_realMetricFn_symm g.form x z c p q
  have htrace (c : RIdx n) : Matrix.trace (A * D c) = 2 * T c := by
    calc
      Matrix.trace (A * D c) = ∑ a, ∑ p, A a p * D c a p := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro p _
        rw [hD c p a]
      _ = 2 * T c := (kahler_metric_derivative_trace g hK x c).symm
  have hsum : (∑ a, rDeriv (fun w => Real.sqrt (realMetricFn g.form x w).det *
      (realMetricFn g.form x w)⁻¹ a b) z a) =
      (∑ a, (ρ / 2 * Matrix.trace (A * D a) * A a b -
        ρ * ((A * D a * A) a b))) := by
    apply Finset.sum_congr rfl
    intro a _
    exact rDeriv_density_inverse_entry g x (mem_extChartAt_target x) a b a
  rw [hsum]
  rw [sum_density_inverse_derivative_form]
  change ρ / 2 * (∑ a, A a b * Matrix.trace (A * D a)) -
    ρ * (∑ a, A a b * T a) = 0
  simp_rw [htrace]
  have hscale : (∑ a, A a b * (2 * T a)) = 2 * (∑ a, A a b * T a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hscale]
  ring

/-- Directional coordinate derivatives obey the ordinary product rule. -/
theorem rDeriv_mul {n : ℕ} {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hk : DifferentiableAt ℝ k z) (a : RIdx n) :
    rDeriv (fun w => f w * k w) z a =
      rDeriv f z a * k z + f z * rDeriv k z a := by
  unfold rDeriv
  rw [fderiv_fun_mul hf hk]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Finite coordinate differentiation, without hidden within derivatives. -/
theorem rDeriv_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → ComplexVector n → ℝ) {z : ComplexVector n}
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) (a : RIdx n) :
    rDeriv (fun w => ∑ i, F i w) z a = ∑ i, rDeriv (F i) z a := by
  unfold rDeriv
  rw [fderiv_fun_sum (fun i _ => hF i)]
  simp only [ContinuousLinearMap.sum_apply]

/-- An actual C² scalar and differentiable matrix coefficient field satisfy
 the coordinate divergence product identity. -/
theorem divergence_matrix_gradient {n : ℕ}
    (B : RIdx n → RIdx n → ComplexVector n → ℝ)
    {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hB : ∀ a b, DifferentiableAt ℝ (B a b) z) (hf : ContDiffAt ℝ 2 f z) :
    (∑ a, rDeriv (fun w => ∑ b, B a b w * rDeriv f w b) z a) =
      (∑ b, (∑ a, rDeriv (B a b) z a) * rDeriv f z b) +
        ∑ a, ∑ b, B a b z * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b) := by
  have hdf (b : RIdx n) : DifferentiableAt ℝ (fun w => rDeriv f w b) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const (realVec b))
  have hrow (a : RIdx n) :
      rDeriv (fun w => ∑ b, B a b w * rDeriv f w b) z a =
      ∑ b, (rDeriv (B a b) z a * rDeriv f z b +
        B a b z * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b)) := by
    calc
      _ = ∑ b, rDeriv (fun w => B a b w * rDeriv f w b) z a :=
        rDeriv_sum (fun b w => B a b w * rDeriv f w b)
          (fun b => (hB a b).mul (hdf b)) a
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        rw [rDeriv_mul (hB a b) (hdf b), rDeriv_rDeriv_eq_hessian hf]
  simp_rw [hrow, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact (Finset.sum_mul _ _ _).symm

/-- The computed real Riemannian flux has exactly twice the project's
 complex Laplacian, with its actual volume density, at each chart center. -/
theorem kahler_scalarMetricFlux_divergence_center {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (x : M.Carrier) :
    (∑ a, rDeriv (scalarMetricFlux g.form x u a) (chartPt x x) a) =
      2 * Real.sqrt (realMetricFn g.form x (chartPt x x)).det * laplacian g.form u x := by
  let z := chartPt x x
  let ρ := Real.sqrt (realMetricFn g.form x z).det
  let B : RIdx n → RIdx n → ComplexVector n → ℝ := fun a b w =>
    Real.sqrt (realMetricFn g.form x w).det * (realMetricFn g.form x w)⁻¹ a b
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hB (a b : RIdx n) : DifferentiableAt ℝ (B a b) z :=
    (((volumeDensity_contDiffOn g x).mul
      (realMetricFn_inverse_contDiffOn g x a b)).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hf : ContDiffAt ℝ 2 (inChart x u) z :=
    ((hu x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hflux (a : RIdx n) : scalarMetricFlux g.form x u a =
      (fun w => ∑ b, B a b w * rDeriv (inChart x u) w b) := by
    funext w
    simp only [scalarMetricFlux, B, Finset.mul_sum, mul_assoc]
  have hfirst : (∑ b, (∑ a, rDeriv (B a b) z a) * rDeriv (inChart x u) z b) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    have hzero : (∑ a, rDeriv (B a b) z a) = 0 :=
      kahler_density_inverse_divergence_center g hK x b
    rw [hzero, zero_mul]
  have hstart : (∑ a, rDeriv (scalarMetricFlux g.form x u a) z a) =
      (∑ a, rDeriv (fun w => ∑ b, B a b w * rDeriv (inChart x u) w b) z a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hflux]
  rw [hstart, divergence_matrix_gradient B hB hf, hfirst, zero_add]
  calc
    (∑ a, ∑ b, B a b z *
      fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) =
        ρ * (∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
          fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change (ρ * (realMetricFn g.form x z)⁻¹ a b) * _ =
        ρ * ((realMetricFn g.form x z)⁻¹ a b * _)
      ring
    _ = ρ * (2 * traceWith (hMat g.form x z) (leviC (inChart x u) z)) :=
      congrArg (fun q => ρ * q)
        (principal_realLaplacian_eq_twice_traceWith g.form x hz hf)
    _ = 2 * Real.sqrt (realMetricFn g.form x (chartPt x x)).det * laplacian g.form u x := by
      change ρ * (2 * laplacian g.form u x) = 2 * ρ * laplacian g.form u x
      ring

/-- Differentiating the actual pullback of a bilinear field gives its tensor
 derivative and the two second-derivative terms of the coordinate map. -/
theorem fderiv_pullback_bilin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hB : DifferentiableAt ℝ B (f x)) (u v w : E) :
    fderiv ℝ (fun y => B (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) x w =
      fderiv ℝ B (f x) (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v) +
        B (f x) (fderiv ℝ (fderiv ℝ f) x w u) (fderiv ℝ f x v) +
          B (f x) (fderiv ℝ f x u) (fderiv ℝ (fderiv ℝ f) x w v) :=
  SharedCalculus.fderiv_pullback_bilin hf hB u v w

/-- The cyclic derivative of a skew bilinear field is tensorial under a
 genuine C² coordinate map; all second-derivative contributions cancel. -/
theorem cyclic_derivative_pullback_bilin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hB : DifferentiableAt ℝ B (f x))
    (hskew : ∀ p q, B (f x) p q = -B (f x) q p) (u v w : E) :
    fderiv ℝ (fun y => B (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) x u +
      fderiv ℝ (fun y => B (f y) (fderiv ℝ f y w) (fderiv ℝ f y u)) x v +
      fderiv ℝ (fun y => B (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) x w =
    fderiv ℝ B (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) (fderiv ℝ f x w) +
      fderiv ℝ B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) (fderiv ℝ f x u) +
      fderiv ℝ B (f x) (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v) :=
  SharedCalculus.cyclic_derivative_pullback_bilin hf hB hskew u v w

/-- Every entry of the project's actual Levi--Civita coordinate calculator
 is smooth on its chart target. -/
theorem christoffel_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (c a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => christoffel g.form x z c a b) (chartTarget x) := by
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro d _
  apply (realMetricFn_inverse_contDiffOn g x c d).mul
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  exact ((rDeriv_contDiffOn hO (metricSmooth_of_smoothMetric g x b d) a).add
    (rDeriv_contDiffOn hO (metricSmooth_of_smoothMetric g x a d) b)).sub
      (rDeriv_contDiffOn hO (metricSmooth_of_smoothMetric g x a b) d)

/-- Actual holomorphic coordinate changes are smooth on chart overlaps. -/
theorem chartTransition_contDiffAt {n : ℕ} {M : ComplexManifold n} (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    ContDiffAt ℂ ∞ (fun w => chartPt b (chartInv a w)) z := by
  have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (chartInv a) z :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) a).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)
  have ho : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ (chartPt b) (chartInv a z) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hy)
  exact (ho.comp z hi).contDiffAt

/-- The actual chart derivative transports inverse-chart frames. -/
theorem chartTransition_fderiv {n : ℕ} {M : ComplexManifold n} (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v : ComplexVector n) :
    fderiv ℂ (fun w => chartPt b (chartInv a w)) z v =
      tangentCoords b (chartInv a z) (chartVec a (chartInv a z) v) := by
  have hi : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) (chartInv a) z := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := ComplexModel n) hz
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have ho : MDifferentiableAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) (chartPt b) (chartInv a z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hy)
  have hcomp := mfderiv_comp_apply z ho hi v
  have hpt : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
  rw [mfderiv_eq_fderiv] at hcomp
  change fderiv ℂ (fun w => chartPt b (chartInv a w)) z v =
    mfderiv (ComplexModel n) (ComplexModel n) (chartPt b) (chartInv a z)
      (mfderiv (ComplexModel n) (ComplexModel n) (chartInv a) z v) at hcomp
  unfold tangentCoords chartVec
  rw [hpt]
  exact hcomp


/-- Multiplication by `I`, regarded as an actual real continuous linear map. -/
def complexStructureCLM (n : ℕ) : ComplexVector n →L[ℝ] ComplexVector n :=
  (Complex.I • ContinuousLinearMap.id ℂ (ComplexVector n)).restrictScalars ℝ

/-- The Kähler two-form as a continuous bilinear field in a genuine chart.
 Its metric is the already constructed real Riemannian metric `2 Re h`. -/
def chartKahlerBilin {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  (L12Aux.realMetricInChart h x z).comp (complexStructureCLM n)

theorem chartKahlerBilin_apply {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v w : ComplexVector n) :
    chartKahlerBilin h x z v w =
      2 * ((h (chartInv x z)).toFun (chartVec x (chartInv x z) v)
        (chartVec x (chartInv x z) w)).im := by
  change L12Aux.realMetricInChart h x z (Complex.I • v) w = _
  rw [L12Aux.realMetricInChart_apply, L12Aux.underlyingRealRiemannianMetric_inner,
    L12Aux.realTangentEquiv_realChartVec x z (Complex.I • v) hz,
    L12Aux.realTangentEquiv_realChartVec x z w hz,
    chartVec_smul, (h (chartInv x z)).map_smul_left]
  simp [Complex.mul_re]

theorem chartKahlerBilin_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartKahlerBilin g.form x) (chartTarget x) :=
  (L12Aux.realMetricInChart_smooth g x).clm_comp contDiffOn_const

theorem chartKahlerBilin_realVec {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    chartKahlerBilin h x z (realVec a) (realVec b) = kahlerFormFn h x z a b :=
  chartKahlerBilin_apply h x hz (realVec a) (realVec b)

theorem chartKahlerBilin_skew {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v w : ComplexVector n) :
    chartKahlerBilin h x z v w = -chartKahlerBilin h x z w v := by
  rw [chartKahlerBilin_apply h x hz, chartKahlerBilin_apply h x hz]
  have hs := congrArg Complex.im ((h (chartInv x z)).conjugate_symmetric
    (chartVec x (chartInv x z) v) (chartVec x (chartInv x z) w))
  simp only [Complex.star_def, Complex.conj_im] at hs
  linarith

/-- The trace of the actual Christoffel symbols is half the metric's
 logarithmic determinant derivative, in every chart and without Kähler closure. -/
theorem christoffel_trace {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a : RIdx n) :
    (∑ b, christoffel h x z b a b) = (1 / 2 : ℝ) *
      Matrix.trace ((realMetricFn h x z)⁻¹ *
        (Matrix.of fun p q => rDeriv (fun w => realMetricFn h x w p q) z a)) := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn h x z)⁻¹
  let D : RIdx n → Matrix (RIdx n) (RIdx n) ℝ := fun c =>
    Matrix.of fun p q => rDeriv (fun w => realMetricFn h x w p q) z c
  have hA (p q : RIdx n) : A p q = A q p :=
    (realMetricFn_isSymm h x z).inv.apply q p
  have hD (c p q : RIdx n) : D c p q = D c q p :=
    rDeriv_realMetricFn_symm h x z c p q
  have hswap : (∑ b, ∑ d, A b d * D b a d) = ∑ b, ∑ d, A b d * D d a b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    rw [hA d b]
  have htrace : (∑ b, ∑ d, A b d * D a b d) = Matrix.trace (A * D a) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    rw [hD a b d]
  change (∑ b, (1 / 2 : ℝ) * ∑ d, A b d * (D a b d + D b a d - D d a b)) = _
  rw [← Finset.mul_sum]
  congr 1
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hswap, htrace]
  ring

/-- The actual volume density obeys the connection trace formula on every
 chart target; this is the scalar density identity used by local Green formulas. -/
theorem rDeriv_volumeDensity_eq_christoffel_trace {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a : RIdx n) :
    rDeriv (fun w => Real.sqrt (realMetricFn g.form x w).det) z a =
      Real.sqrt (realMetricFn g.form x z).det * ∑ b, christoffel g.form x z b a b := by
  rw [christoffel_trace]
  exact (fderiv_volumeDensity g x hz (realVec a)).trans (by
    simp only [rDeriv]
    ring)

/-- Evaluation on fixed vectors commutes with differentiation of the genuine
 continuous bilinear coefficient field. -/
theorem fderiv_bilin_apply_const {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : E → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (u : E) (v w : F) :
    fderiv ℝ (fun y => B y v w) x u = fderiv ℝ B x u v w :=
  SharedCalculus.fderiv_bilin_apply_const hB u v w

/-- A cyclic trilinear expression vanishing on a basis vanishes on all
 vectors. The three uses of basis extensionality are actual linear maps. -/
theorem cyclic_trilinear_zero_of_basis {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : Module.Basis ι ℝ E)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h : ∀ i j k, D (e i) (e j) (e k) + D (e j) (e k) (e i) +
      D (e k) (e i) (e j) = 0) (u v w : E) :
    D u v w + D v w u + D w u v = 0 :=
  SharedCalculus.cyclic_trilinear_zero_of_basis e D h u v w

/-- The two-form in two genuine charts is related by the actual pullback
 derivative of their holomorphic coordinate change. -/
theorem chartKahlerBilin_pullback {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v w : ComplexVector n) :
    chartKahlerBilin h a z v w =
      chartKahlerBilin h b (chartPt b (chartInv a z))
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z v)
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z w) := by
  have hd : DifferentiableAt ℂ (fun t => chartPt b (chartInv a t)) z :=
    (chartTransition_contDiffAt a b hz hy).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  change chartKahlerBilin h a z v w =
    chartKahlerBilin h b (chartPt b (chartInv a z))
      (fderiv ℂ (fun t => chartPt b (chartInv a t)) z v)
      (fderiv ℂ (fun t => chartPt b (chartInv a t)) z w)
  have ht : chartPt b (chartInv a z) ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source hy
  have hinv : chartInv b (chartPt b (chartInv a z)) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  rw [chartTransition_fderiv a b hz hy v, chartTransition_fderiv a b hz hy w,
    chartKahlerBilin_apply h a hz, chartKahlerBilin_apply h b ht]
  rw [hinv,
    L12Aux.chartVec_tangentCoords b (chartInv a z) hy,
    L12Aux.chartVec_tangentCoords b (chartInv a z) hy]

/-- Differentiating the continuous bilinear field recovers exactly each
 coordinate derivative of the project's Kähler-form coefficients. -/
theorem fderiv_chartKahlerBilin_realVec {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    fderiv ℝ (chartKahlerBilin g.form x) z (realVec a) (realVec b) (realVec c) =
      rDeriv (fun t => kahlerFormFn g.form x t b c) z a := by
  have hB : DifferentiableAt ℝ (chartKahlerBilin g.form x) z :=
    ((chartKahlerBilin_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun t => chartKahlerBilin g.form x t (realVec b) (realVec c)) =ᶠ[𝓝 z]
      (fun t => kahlerFormFn g.form x t b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with t ht
    exact chartKahlerBilin_realVec g.form x ht b c
  rw [← fderiv_bilin_apply_const hB]
  exact congrArg (fun A => A (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))

/-- The pointwise Kähler hypothesis on the fixed real basis extends to all
 real tangent directions of the center chart. -/
theorem cyclic_chartKahlerBilin_center {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x) u v w +
      fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x) v w u +
      fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x) w u v = 0 := by
  apply cyclic_trilinear_zero_of_basis (complexVector_realOrthonormalBasis n).toBasis
    (fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x)) _ u v w
  intro a b c
  change fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x)
    (complexVector_realOrthonormalBasis n a) (complexVector_realOrthonormalBasis n b)
      (complexVector_realOrthonormalBasis n c) +
    fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x)
      (complexVector_realOrthonormalBasis n b) (complexVector_realOrthonormalBasis n c)
        (complexVector_realOrthonormalBasis n a) +
    fderiv ℝ (chartKahlerBilin g.form x) (chartPt x x)
      (complexVector_realOrthonormalBasis n c) (complexVector_realOrthonormalBasis n a)
        (complexVector_realOrthonormalBasis n b) = 0
  simp only [complexVector_realOrthonormalBasis_apply]
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [fderiv_chartKahlerBilin_realVec g x hz,
    fderiv_chartKahlerBilin_realVec g x hz,
    fderiv_chartKahlerBilin_realVec g x hz]
  exact hK x a b c

/-- The pointwise Kähler condition is transported to all points of any
 fixed chart by the proved tensorial cyclic derivative identity. -/
theorem cyclic_chartKahlerBilin_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin g.form x) z u v w +
      fderiv ℝ (chartKahlerBilin g.form x) z v w u +
      fderiv ℝ (chartKahlerBilin g.form x) z w u v = 0 := by
  let y := chartInv x z
  let T : ComplexVector n → ComplexVector n := fun t => chartPt y (chartInv x t)
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have ht : T z ∈ chartTarget y := mem_extChartAt_target y
  have hT : ContDiffAt ℝ 2 T z :=
    ((chartTransition_contDiffAt x y hz hy).restrict_scalars ℝ).of_le (by simp)
  have hBx : DifferentiableAt ℝ (chartKahlerBilin g.form x) z :=
    ((chartKahlerBilin_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hBy : DifferentiableAt ℝ (chartKahlerBilin g.form y) (T z) :=
    ((chartKahlerBilin_contDiffOn g y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds ht)).differentiableAt (by simp)
  have hskew (p q : ComplexVector n) :
      chartKahlerBilin g.form y (T z) p q = -chartKahlerBilin g.form y (T z) q p :=
    chartKahlerBilin_skew g.form y ht p q
  have hi : ContinuousAt (chartInv x) z := continuousAt_extChartAt_symm'' hz
  have hs : ∀ᶠ t in 𝓝 z, chartInv x t ∈ (extChartAt (ComplexModel n) y).source :=
    hi.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds hy)
  have hpull (p q : ComplexVector n) :
      (fun t => chartKahlerBilin g.form x t p q) =ᶠ[𝓝 z]
        (fun t => chartKahlerBilin g.form y (T t) (fderiv ℝ T t p) (fderiv ℝ T t q)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz, hs]
      with t htx hty
    exact chartKahlerBilin_pullback g.form x y htx hty p q
  have hderiv (p q r : ComplexVector n) :
      fderiv ℝ (chartKahlerBilin g.form x) z p q r =
        fderiv ℝ (fun t => chartKahlerBilin g.form y (T t)
          (fderiv ℝ T t q) (fderiv ℝ T t r)) z p := by
    rw [← fderiv_bilin_apply_const hBx]
    exact congrArg (fun A => A p) ((hpull q r).fderiv_eq (𝕜 := ℝ))
  rw [hderiv u v w, hderiv v w u, hderiv w u v]
  exact (cyclic_derivative_pullback_bilin hT hBy hskew u v w).trans
    (cyclic_chartKahlerBilin_center g hK y
      (fderiv ℝ T z u) (fderiv ℝ T z v) (fderiv ℝ T z w))

/-- The exact coordinate Kähler closure equation holds throughout every
 actual chart target, rather than only at its chosen center. -/
theorem kahlerClosed_in_chart {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun t => kahlerFormFn g.form x t b c) z a +
      rDeriv (fun t => kahlerFormFn g.form x t c a) z b +
      rDeriv (fun t => kahlerFormFn g.form x t a b) z c = 0 := by
  have hc := cyclic_chartKahlerBilin_on g hK x hz (realVec a) (realVec b) (realVec c)
  rw [fderiv_chartKahlerBilin_realVec g x hz,
    fderiv_chartKahlerBilin_realVec g x hz, fderiv_chartKahlerBilin_realVec g x hz] at hc
  exact hc

/-- Kähler derivative identity throughout the actual fixed chart target. -/
theorem kahler_metric_derivative_identity_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b d : RIdx n) :
    -rDeriv (fun w => realMetricFn g.form x w b d) z a +
      jSign b * jSign d * rDeriv
        (fun w => realMetricFn g.form x w (jIndex n d) a) z (jIndex n b) +
      rDeriv (fun w => realMetricFn g.form x w a b) z d = 0 := by
  have hk := kahlerClosed_in_chart g hK x hz a (jIndex n b) d
  have h1 : (fun w => kahlerFormFn g.form x w (jIndex n b) d) =
      (fun w => (-jSign b) * realMetricFn g.form x w b d) := by
    funext w
    exact kahlerFormFn_jIndex_left g.form x w b d
  have h2 : (fun w => kahlerFormFn g.form x w d a) =
      (fun w => jSign d * realMetricFn g.form x w (jIndex n d) a) := by
    funext w
    exact kahlerFormFn_eq_jIndex_metric g.form x w d a
  have h3 : (fun w => kahlerFormFn g.form x w a (jIndex n b)) =
      (fun w => jSign b * realMetricFn g.form x w a b) := by
    funext w
    exact kahlerFormFn_jIndex_right g.form x w a b
  change rDeriv _ z a + rDeriv _ z (jIndex n b) +
    rDeriv _ z d = 0 at hk
  have hG (p q : RIdx n) :
      DifferentiableAt ℝ (fun w => realMetricFn g.form x w p q) z :=
    realMetricFn_differentiableAt g x hz p q
  rw [h1, h2, h3,
    rDeriv_const_mul (hG b d) (-jSign b) a,
    rDeriv_const_mul (hG (jIndex n d) a) (jSign d) (jIndex n b),
    rDeriv_const_mul (hG a b) (jSign b) d] at hk
  by_cases hb : b.2 = 0
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith

/-- The Kähler derivative contraction holds throughout each fixed chart. -/
theorem kahler_metric_derivative_trace_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (d : RIdx n) :
    2 * (∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
      rDeriv (fun w => realMetricFn g.form x w b d) z a) =
      ∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
        rDeriv (fun w => realMetricFn g.form x w a b) z d := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form x z)⁻¹
  let D : RIdx n → RIdx n → RIdx n → ℝ := fun a b c =>
    rDeriv (fun w => realMetricFn g.form x w b c) z a
  have hJA (a b : RIdx n) : A (jIndex n a) (jIndex n b) = jSign a * jSign b * A a b := by
    simpa only [A, chartPt] using
      realMetricFn_inverse_jIndex g.form x hz a b
  have hJD (a b c : RIdx n) : D a (jIndex n b) (jIndex n c) = jSign b * jSign c * D a b c :=
    rDeriv_realMetricFn_jIndex g x hz a b c
  have hSA (a b : RIdx n) : A b a = A a b := by
    simpa only [A] using (realMetricFn_isSymm g.form x z).inv.apply a b
  have hSD (a b c : RIdx n) : D a b c = D a c b :=
    rDeriv_realMetricFn_symm g.form x z a b c
  let T := ∑ a, ∑ b, A a b * D a b d
  let U := ∑ a, ∑ b, A a b * jSign b * jSign d * D (jIndex n b) (jIndex n d) a
  let S := ∑ a, ∑ b, A a b * D d a b
  have hU : U = -T := by
    have hterm (a b : RIdx n) :
        A (jIndex n a) (jIndex n b) * jSign (jIndex n b) * jSign d *
          D (jIndex n (jIndex n b)) (jIndex n d) (jIndex n a) = -A a b * D b d a := by
      rw [hJA, jSign_jIndex, jIndex_involutive, hJD]
      calc
        _ = -(jSign a * jSign a) * (jSign b * jSign b) * (jSign d * jSign d) *
            (A a b * D b d a) := by ring
        _ = -A a b * D b d a := by rw [jSign_sq, jSign_sq, jSign_sq]; ring
    calc
      U = ∑ a, ∑ b, A (jIndex n a) (jIndex n b) * jSign (jIndex n b) * jSign d *
          D (jIndex n (jIndex n b)) (jIndex n d) (jIndex n a) :=
        (sum_jIndex_two (fun a b => A a b * jSign b * jSign d *
          D (jIndex n b) (jIndex n d) a)).symm
      _ = ∑ a, ∑ b, -A a b * D b d a := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact hterm a b
      _ = -(∑ a, ∑ b, A a b * D b d a) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
      _ = -T := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hSA, hSD]
  have hsum : -T + U + S = 0 := by
    have hzero : (∑ a, ∑ b, A a b *
        (-D a b d + jSign b * jSign d * D (jIndex n b) (jIndex n d) a + D d a b)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      rw [show -D a b d + jSign b * jSign d * D (jIndex n b) (jIndex n d) a + D d a b = 0 from
        kahler_metric_derivative_identity_on g hK x hz a b d]
      exact mul_zero _
    simpa only [T, U, S, mul_add, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, mul_assoc] using hzero
  have hfinal : 2 * T = S := by linarith
  simpa only [T, S, A, D] using hfinal

/-- The actual density-weighted inverse metric is divergence free on
 every Kähler chart target, with no additional closure premise. -/
theorem kahler_density_inverse_divergence_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (b : RIdx n) :
    (∑ a, rDeriv (fun w => Real.sqrt (realMetricFn g.form x w).det *
      (realMetricFn g.form x w)⁻¹ a b) z a) = 0 := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form x z)⁻¹
  let D : RIdx n → Matrix (RIdx n) (RIdx n) ℝ := fun c =>
    Matrix.of fun p q => rDeriv (fun w => realMetricFn g.form x w p q) z c
  let ρ := Real.sqrt (realMetricFn g.form x z).det
  let T : RIdx n → ℝ := fun c => ∑ a, ∑ p, A a p * D a p c
  have hD (c p q : RIdx n) : D c p q = D c q p :=
    rDeriv_realMetricFn_symm g.form x z c p q
  have htrace (c : RIdx n) : Matrix.trace (A * D c) = 2 * T c := by
    calc
      Matrix.trace (A * D c) = ∑ a, ∑ p, A a p * D c a p := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro p _
        rw [hD c p a]
      _ = 2 * T c := (kahler_metric_derivative_trace_on g hK x hz c).symm
  have hsum : (∑ a, rDeriv (fun w => Real.sqrt (realMetricFn g.form x w).det *
      (realMetricFn g.form x w)⁻¹ a b) z a) =
      (∑ a, (ρ / 2 * Matrix.trace (A * D a) * A a b -
        ρ * ((A * D a * A) a b))) := by
    apply Finset.sum_congr rfl
    intro a _
    exact rDeriv_density_inverse_entry g x hz a b a
  rw [hsum]
  rw [sum_density_inverse_derivative_form]
  change ρ / 2 * (∑ a, A a b * Matrix.trace (A * D a)) -
    ρ * (∑ a, A a b * T a) = 0
  simp_rw [htrace]
  have hscale : (∑ a, A a b * (2 * T a)) = 2 * (∑ a, A a b * T a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hscale]
  ring

/-- Divergence equals twice the actual fixed-chart complex metric trace
 throughout the chart target. Scalar chart invariance is a separate bridge. -/
theorem kahler_scalarMetricFlux_divergence_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    (∑ a, rDeriv (scalarMetricFlux g.form x u a) z a) =
      2 * Real.sqrt (realMetricFn g.form x z).det * traceWith (hMat g.form x z) (leviC (inChart x u) z) := by
  let ρ := Real.sqrt (realMetricFn g.form x z).det
  let B : RIdx n → RIdx n → ComplexVector n → ℝ := fun a b w =>
    Real.sqrt (realMetricFn g.form x w).det * (realMetricFn g.form x w)⁻¹ a b
  have hB (a b : RIdx n) : DifferentiableAt ℝ (B a b) z :=
    (((volumeDensity_contDiffOn g x).mul
      (realMetricFn_inverse_contDiffOn g x a b)).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hf : ContDiffAt ℝ 2 (inChart x u) z :=
    ((hu x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hflux (a : RIdx n) : scalarMetricFlux g.form x u a =
      (fun w => ∑ b, B a b w * rDeriv (inChart x u) w b) := by
    funext w
    simp only [scalarMetricFlux, B, Finset.mul_sum, mul_assoc]
  have hfirst : (∑ b, (∑ a, rDeriv (B a b) z a) * rDeriv (inChart x u) z b) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    have hzero : (∑ a, rDeriv (B a b) z a) = 0 :=
      kahler_density_inverse_divergence_on g hK x hz b
    rw [hzero, zero_mul]
  have hstart : (∑ a, rDeriv (scalarMetricFlux g.form x u a) z a) =
      (∑ a, rDeriv (fun w => ∑ b, B a b w * rDeriv (inChart x u) w b) z a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hflux]
  rw [hstart, divergence_matrix_gradient B hB hf, hfirst, zero_add]
  calc
    (∑ a, ∑ b, B a b z *
      fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) =
        ρ * (∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
          fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change (ρ * (realMetricFn g.form x z)⁻¹ a b) * _ =
        ρ * ((realMetricFn g.form x z)⁻¹ a b * _)
      ring
    _ = ρ * (2 * traceWith (hMat g.form x z) (leviC (inChart x u) z)) :=
      congrArg (fun q => ρ * q)
        (principal_realLaplacian_eq_twice_traceWith g.form x hz hf)
    _ = 2 * Real.sqrt (realMetricFn g.form x z).det * traceWith (hMat g.form x z) (leviC (inChart x u) z) := by
      change ρ * (2 * traceWith (hMat g.form x z) (leviC (inChart x u) z)) = 2 * ρ * traceWith (hMat g.form x z) (leviC (inChart x u) z)
      ring

/-- Green's identity for the actual fixed-chart complex metric trace,
 including the proved positive real/complex factor and volume density. -/
theorem integral_kahler_chart_trace {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * (2 * Real.sqrt (realMetricFn g.form x z).det *
      traceWith (hMat g.form x z) (leviC (inChart x u) z)) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * scalarMetricFlux g.form x u a z ∂lebesgueC n) := by
  have heq : (fun z => φ z * (∑ a, rDeriv (scalarMetricFlux g.form x u a) z a)) =
      (fun z => φ z * (2 * Real.sqrt (realMetricFn g.form x z).det *
        traceWith (hMat g.form x z) (leviC (inChart x u) z))) := by
    funext z
    by_cases hzero : φ z = 0
    · simp only [hzero, zero_mul]
    · have hz : z ∈ chartTarget x := hφO (subset_closure hzero)
      rw [kahler_scalarMetricFlux_divergence_on g hK hu x hz]
  rw [← heq]
  exact integral_scalarMetricFlux g hu x hφ hcφ hφO

/-- The genuine real Hessian chain rule, with every first derivative justified
 on an actual neighborhood rather than treated as formal data. -/
theorem secondFDeriv_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {u : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hu : ContDiffAt ℝ 2 u (f x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (u ∘ f)) x v w =
      fderiv ℝ (fderiv ℝ u) (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) +
        fderiv ℝ u (f x) (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hfdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hudd : DifferentiableAt ℝ (fderiv ℝ u) (f x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hunear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u (f y) :=
    hf.continuousAt.eventually (hu.eventually (by norm_num))
  have heq : fderiv ℝ (u ∘ f) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ u (f y)).comp (fderiv ℝ f y)) := by
    filter_upwards [hf.eventually (by norm_num), hunear] with y hfy huy
    exact fderiv_comp y (huy.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))
  have hcomp : DifferentiableAt ℝ (fun y => fderiv ℝ u (f y)) x :=
    DifferentiableAt.comp (g := fderiv ℝ u) (f := f) x hudd hfd
  have hdc : fderiv ℝ (fun y => fderiv ℝ u (f y)) x =
      (fderiv ℝ (fderiv ℝ u) (f x)).comp (fderiv ℝ f x) :=
    fderiv_comp (g := fderiv ℝ u) x hudd hfd
  rw [heq.fderiv_eq, fderiv_clm_comp hcomp hfdd, hdc]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  ring

/-- For a genuine C² holomorphic map, the actual second real derivative
 is the scalar restriction of its complex second derivative. -/
theorem secondFDeriv_restrict_complex {n m : ℕ}
    {f : ComplexVector n → ComplexVector m} {z : ComplexVector n}
    (hf : ContDiffAt ℂ 2 f z) (v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℂ (fderiv ℂ f) z v w := by
  have h := congrArg (fun A => A ![v, w]) (hf.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  simpa only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h.symm

/-- The real Hessian of a holomorphic coordinate map is complex bilinear. -/
theorem secondFDeriv_complex_I_I {n m : ℕ}
    {f : ComplexVector n → ComplexVector m} {z : ComplexVector n}
    (hf : ContDiffAt ℂ 2 f z) (v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • w) =
      -fderiv ℝ (fderiv ℝ f) z v w := by
  rw [secondFDeriv_restrict_complex hf, secondFDeriv_restrict_complex hf]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

/-- The actual real coordinate basis realizes the signed complex structure. -/
theorem realVec_jIndex {n : ℕ} (a : RIdx n) :
    realVec (jIndex n a) = jSign a • (Complex.I • realVec a) := by
  rcases a with ⟨i, a⟩
  fin_cases a <;> simp [jIndex, jSign, realVec, smul_smul, Complex.I_mul_I]

/-- Every genuine holomorphic coordinate component has zero principal
 Hermitian metric trace, including non-diagonal metrics. -/
theorem inverseMetric_holomorphic_second_trace {n m : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) {f : ComplexVector n → ComplexVector m}
    (hf : ContDiffAt ℂ 2 f z) (L : ComplexVector m →L[ℝ] ℝ) :
    (∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b *
      L (fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b))) = 0 := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn h x z)⁻¹
  let H : RIdx n → RIdx n → ℝ := fun a b =>
    L (fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b))
  have hA (a b : RIdx n) : A (jIndex n a) (jIndex n b) = jSign a * jSign b * A a b :=
    realMetricFn_inverse_jIndex h x hz a b
  have hH (a b : RIdx n) : H (jIndex n a) (jIndex n b) =
      -(jSign a * jSign b) * H a b := by
    dsimp only [H]
    rw [realVec_jIndex, realVec_jIndex]
    simp only [map_smul, ContinuousLinearMap.smul_apply, secondFDeriv_complex_I_I hf,
      map_neg, smul_eq_mul]
    ring
  have hterm (a b : RIdx n) :
      A (jIndex n a) (jIndex n b) * H (jIndex n a) (jIndex n b) = -A a b * H a b := by
    rw [hA, hH]
    calc
      _ = -(jSign a * jSign a) * (jSign b * jSign b) * (A a b * H a b) := by ring
      _ = -A a b * H a b := by rw [jSign_sq, jSign_sq]; ring
  have heq : (∑ a, ∑ b, A a b * H a b) = -(∑ a, ∑ b, A a b * H a b) := by
    calc
      _ = ∑ a, ∑ b, A (jIndex n a) (jIndex n b) * H (jIndex n a) (jIndex n b) :=
        (sum_jIndex_two (fun a b => A a b * H a b)).symm
      _ = ∑ a, ∑ b, -A a b * H a b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact hterm a b
      _ = -(∑ a, ∑ b, A a b * H a b) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
  change (∑ a, ∑ b, A a b * H a b) = 0
  linarith

/-- The actual matrix of a real continuous linear coordinate map in the
 fixed real orthonormal basis. -/
def realLinearMatrix {n : ℕ} (L : ComplexVector n →L[ℝ] ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  LinearMap.toMatrix (complexVector_realOrthonormalBasis n).toBasis
    (complexVector_realOrthonormalBasis n).toBasis L.toLinearMap

/-- The actual matrix of a continuous real bilinear field in that basis. -/
def realBilinMatrix {n : ℕ} (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  LinearMap.BilinForm.toMatrix (complexVector_realOrthonormalBasis n).toBasis B.toLinearMap₁₂

theorem realBilinMatrix_apply {n : ℕ}
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) (a b : RIdx n) :
    realBilinMatrix B a b = B (realVec a) (realVec b) := by
  unfold realBilinMatrix
  rw [LinearMap.BilinForm.toMatrix_apply]
  change B (complexVector_realOrthonormalBasis n a) (complexVector_realOrthonormalBasis n b) = _
  rw [complexVector_realOrthonormalBasis_apply, complexVector_realOrthonormalBasis_apply]

/-- Continuous bilinear pullback is actual matrix congruence. -/
theorem realBilinMatrix_pullback {n : ℕ}
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (L : ComplexVector n →L[ℝ] ComplexVector n) :
    realBilinMatrix (B.bilinearComp L L) =
      (realLinearMatrix L)ᵀ * realBilinMatrix B * realLinearMatrix L := by
  let e := (complexVector_realOrthonormalBasis n).toBasis
  change LinearMap.BilinForm.toMatrix e (LinearMap.BilinForm.comp B.toLinearMap₁₂ L.toLinearMap L.toLinearMap) = _
  exact LinearMap.BilinForm.toMatrix_comp e e B.toLinearMap₁₂ L.toLinearMap L.toLinearMap

/-- Matrix trace against the inverse transforms correctly under a genuine
 nonsingular coordinate map; the inverse is the actual nonsingular inverse. -/
theorem matrix_inverse_trace_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H D : Matrix ι ι ℝ) (hD : D.det ≠ 0) :
    Matrix.trace ((Dᵀ * G * D)⁻¹ * (Dᵀ * H * D)) = Matrix.trace (G⁻¹ * H) := by
  have hDt : IsUnit (Dᵀ).det := by simpa only [Matrix.det_transpose] using isUnit_iff_ne_zero.mpr hD
  have hcancel : (Dᵀ)⁻¹ * Dᵀ = 1 := Matrix.nonsing_inv_mul _ hDt
  calc
    _ = Matrix.trace (D⁻¹ * (G⁻¹ * H) * D) := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Dᵀ)⁻¹ Dᵀ (H * D), hcancel, Matrix.one_mul]
    _ = Matrix.trace (D * D⁻¹ * (G⁻¹ * H)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (G⁻¹ * H) := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD), Matrix.one_mul]

/-- The continuous real metric field in a genuine chart has exactly the
 project's matrix coefficients. -/
theorem realBilinMatrix_realMetric {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    realBilinMatrix (L12Aux.realMetricInChart h x z) = realMetricFn h x z := by
  ext a b
  rw [realBilinMatrix_apply, L12Aux.realMetricInChart_apply]
  exact L12Aux.underlyingRealRiemannianMetric_frame h x z hz a b

/-- The constructed real metric evaluates to `2 Re h` in the actual
 inverse-chart frame, for arbitrary vectors on the chart target. -/
theorem realMetricInChart_apply_complex {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v w : ComplexVector n) :
    L12Aux.realMetricInChart h x z v w =
      2 * ((h (chartInv x z)).toFun (chartVec x (chartInv x z) v)
        (chartVec x (chartInv x z) w)).re := by
  rw [L12Aux.realMetricInChart_apply, L12Aux.underlyingRealRiemannianMetric_inner,
    L12Aux.realTangentEquiv_realChartVec x z v hz, L12Aux.realTangentEquiv_realChartVec x z w hz]

/-- Actual coordinate transitions pull back the genuine real metric. -/
theorem realMetricInChart_pullback {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v w : ComplexVector n) :
    L12Aux.realMetricInChart h a z v w =
      L12Aux.realMetricInChart h b (chartPt b (chartInv a z))
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z v)
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z w) := by
  have hd : DifferentiableAt ℂ (fun t => chartPt b (chartInv a t)) z :=
    (chartTransition_contDiffAt a b hz hy).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  change L12Aux.realMetricInChart h a z v w =
    L12Aux.realMetricInChart h b (chartPt b (chartInv a z))
      (fderiv ℂ (fun t => chartPt b (chartInv a t)) z v)
      (fderiv ℂ (fun t => chartPt b (chartInv a t)) z w)
  have ht : chartPt b (chartInv a z) ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source hy
  have hinv : chartInv b (chartPt b (chartInv a z)) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  rw [chartTransition_fderiv a b hz hy v, chartTransition_fderiv a b hz hy w,
    realMetricInChart_apply_complex h a hz, realMetricInChart_apply_complex h b ht]
  rw [hinv,
    L12Aux.chartVec_tangentCoords b (chartInv a z) hy,
    L12Aux.chartVec_tangentCoords b (chartInv a z) hy]

/-- The project's Gram determinant never vanishes on its actual chart. -/
theorem realMetricFn_det_ne_zero {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (realMetricFn h x z).det ≠ 0 := by
  rw [realMetricFn_det h x hz]
  exact pow_ne_zero _ (mul_ne_zero (by norm_num) (ne_of_gt (hMat_det_re_pos h x hz)))

/-- The exact project real metric matrices obey the actual coordinate
 congruence rule in every chart overlap. -/
theorem realMetricFn_chart_congruence {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    realMetricFn h a z =
      (realLinearMatrix (fderiv ℝ (fun t => chartPt b (chartInv a t)) z))ᵀ *
        realMetricFn h b (chartPt b (chartInv a z)) *
        realLinearMatrix (fderiv ℝ (fun t => chartPt b (chartInv a t)) z) := by
  let L := fderiv ℝ (fun t => chartPt b (chartInv a t)) z
  have ht : chartPt b (chartInv a z) ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hy
  have hf : L12Aux.realMetricInChart h a z =
      (L12Aux.realMetricInChart h b (chartPt b (chartInv a z))).bilinearComp L L := by
    ext v w
    exact realMetricInChart_pullback h a b hz hy v w
  rw [← realBilinMatrix_realMetric h a hz, hf, realBilinMatrix_pullback,
    realBilinMatrix_realMetric h b ht]

/-- The transition derivative's actual real matrix is nonsingular. This
 follows internally from the genuine metric congruence and positive metric. -/
theorem realChartTransition_det_ne_zero {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    (realLinearMatrix (fderiv ℝ (fun t => chartPt b (chartInv a t)) z)).det ≠ 0 := by
  intro hzero
  apply realMetricFn_det_ne_zero h a hz
  rw [realMetricFn_chart_congruence h a b hz hy, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hzero, zero_mul, zero_mul]

/-- The inverse-metric matrix trace is the actual contraction in the real
 coordinate basis, using the proved symmetry of the genuine inverse metric. -/
theorem realMetric_trace_eq_contraction {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    Matrix.trace ((realMetricFn h x z)⁻¹ * realBilinMatrix B) =
      ∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b * B (realVec a) (realVec b) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, realBilinMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [(realMetricFn_isSymm h x z).inv.apply a b]

/-- Tracing a pulled-back bilinear field against the actual metric inverse
 commutes with a genuine change of charts. -/
theorem realMetric_trace_bilin_pullback {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    Matrix.trace ((realMetricFn h a z)⁻¹ *
      realBilinMatrix (B.bilinearComp
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z)
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z))) =
      Matrix.trace ((realMetricFn h b (chartPt b (chartInv a z)))⁻¹ * realBilinMatrix B) := by
  rw [realMetricFn_chart_congruence h a b hz hy, realBilinMatrix_pullback]
  exact matrix_inverse_trace_congruence _ _ _ (realChartTransition_det_ne_zero h a b hz hy)

/-- Matrix representation preserves actual addition of bilinear forms. -/
theorem realBilinMatrix_add {n : ℕ}
    (B C : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    realBilinMatrix (B + C) = realBilinMatrix B + realBilinMatrix C := by
  ext a b
  simp only [Matrix.add_apply, realBilinMatrix_apply, ContinuousLinearMap.add_apply]

/-- The genuine Hessian's Hermitian metric trace is invariant under the
 actual holomorphic coordinate change. The coordinate drift term vanishes
 by the independently proved holomorphic second-derivative contraction. -/
theorem realMetric_hessian_chart_comp {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    {f : ComplexVector n → ℝ}
    (hf : ContDiffAt ℝ 2 f (chartPt b (chartInv a z))) :
    Matrix.trace ((realMetricFn h a z)⁻¹ *
      realBilinMatrix (fderiv ℝ (fderiv ℝ (f ∘ fun t => chartPt b (chartInv a t))) z)) =
      Matrix.trace ((realMetricFn h b (chartPt b (chartInv a z)))⁻¹ *
        realBilinMatrix (fderiv ℝ (fderiv ℝ f) (chartPt b (chartInv a z)))) := by
  let T : ComplexVector n → ComplexVector n := fun t => chartPt b (chartInv a t)
  let L := fderiv ℝ T z
  let H := fderiv ℝ (fderiv ℝ f) (T z)
  let C : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ
      (fderiv ℝ f (T z))).comp (fderiv ℝ (fderiv ℝ T) z)
  have hTC : ContDiffAt ℂ 2 T z := (chartTransition_contDiffAt a b hz hy).of_le (by simp)
  have hTR : ContDiffAt ℝ 2 T z := hTC.restrict_scalars ℝ
  have hH : fderiv ℝ (fderiv ℝ (f ∘ T)) z = H.bilinearComp L L + C := by
    ext v w
    change fderiv ℝ (fderiv ℝ (f ∘ T)) z v w =
      fderiv ℝ (fderiv ℝ f) (T z) (fderiv ℝ T z v) (fderiv ℝ T z w) +
        fderiv ℝ f (T z) (fderiv ℝ (fderiv ℝ T) z v w)
    exact secondFDeriv_comp hTR hf v w
  have hzero : Matrix.trace ((realMetricFn h a z)⁻¹ * realBilinMatrix C) = 0 := by
    rw [realMetric_trace_eq_contraction]
    exact inverseMetric_holomorphic_second_trace h a hz hTC (fderiv ℝ f (T z))
  change Matrix.trace ((realMetricFn h a z)⁻¹ * realBilinMatrix (fderiv ℝ (fderiv ℝ (f ∘ T)) z)) = _
  rw [hH, realBilinMatrix_add, Matrix.mul_add, Matrix.trace_add, hzero, add_zero]
  exact realMetric_trace_bilin_pullback h a b hz hy H

/-- The project's scalar complex Laplacian is exactly the same metric trace
 in every actual chart. This is proved from actual Hessians and metric
 pullback, with no Kähler, completeness or curvature premise. -/
theorem traceWith_inChart_eq_laplacian {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    traceWith (hMat h a z) (leviC (inChart a u) z) = laplacian h u (chartInv a z) := by
  let b := chartInv a z
  let T : ComplexVector n → ComplexVector n := fun t => chartPt b (chartInv a t)
  have hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source := mem_extChartAt_source b
  have ht : T z ∈ chartTarget b := mem_extChartAt_target b
  have hfA : ContDiffAt ℝ 2 (inChart a u) z :=
    ((hu a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).of_le (by simp)
  have hfB : ContDiffAt ℝ 2 (inChart b u) (T z) :=
    ((hu b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds ht)).of_le (by simp)
  have hi : ContinuousAt (chartInv a) z := continuousAt_extChartAt_symm'' hz
  have hs : ∀ᶠ t in 𝓝 z, chartInv a t ∈ (extChartAt (ComplexModel n) b).source :=
    hi.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) b).mem_nhds hy)
  have heq : inChart a u =ᶠ[𝓝 z] ((inChart b u) ∘ T) := by
    filter_upwards [hs] with t hty
    exact congrArg u ((extChartAt (ComplexModel n) b).left_inv hty).symm
  have hH : fderiv ℝ (fderiv ℝ (inChart a u)) z =
      fderiv ℝ (fderiv ℝ ((inChart b u) ∘ T)) z :=
    (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hp := realMetric_hessian_chart_comp h a b hz hy hfB
  change Matrix.trace ((realMetricFn h a z)⁻¹ *
    realBilinMatrix (fderiv ℝ (fderiv ℝ ((inChart b u) ∘ T)) z)) =
      Matrix.trace ((realMetricFn h b (T z))⁻¹ *
        realBilinMatrix (fderiv ℝ (fderiv ℝ (inChart b u)) (T z))) at hp
  rw [← hH, realMetric_trace_eq_contraction h a z,
    realMetric_trace_eq_contraction h b (T z)] at hp
  have htwo : 2 * traceWith (hMat h a z) (leviC (inChart a u) z) =
      2 * traceWith (hMat h b (T z)) (leviC (inChart b u) (T z)) :=
    (principal_realLaplacian_eq_twice_traceWith h a hz hfA).symm.trans
      (hp.trans (principal_realLaplacian_eq_twice_traceWith h b ht hfB))
  change traceWith (hMat h a z) (leviC (inChart a u) z) =
    traceWith (hMat h b (T z)) (leviC (inChart b u) (T z))
  linarith

/-- The actual scalar metric Laplacian of a smooth function is smooth.
 The pointwise definition is identified with each fixed chart internally. -/
theorem smoothFn_laplacian {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {u : M.Carrier → ℝ} (hu : SmoothFn u) :
    SmoothFn (laplacian g.form u) := by
  intro x
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hdu : ContDiffOn ℝ ∞ (fderiv ℝ (inChart x u)) (chartTarget x) :=
    (hu x).fderiv_of_isOpen hO (by simp)
  have hddu : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (inChart x u))) (chartTarget x) :=
    hdu.fderiv_of_isOpen hO (by simp)
  have hp : ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * ∑ a, ∑ b,
      (realMetricFn g.form x z)⁻¹ a b *
        fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) (chartTarget x) := by
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro a _
    apply ContDiffOn.sum
    intro b _
    exact (realMetricFn_inverse_contDiffOn g x a b).mul
      ((hddu.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  apply hp.congr
  intro z hz
  symm
  have hf : ContDiffAt ℝ 2 (inChart x u) z :=
    ((hu x).contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  change (1 / 2 : ℝ) * (∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
    fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) = laplacian g.form u (chartInv x z)
  rw [principal_realLaplacian_eq_twice_traceWith g.form x hz hf,
    traceWith_inChart_eq_laplacian g.form hu x hz]
  ring

/-- The true chart flux computes twice the project's intrinsic scalar
 Laplacian, with its actual Riemannian density, everywhere in the chart. -/
theorem kahler_scalarMetricFlux_divergence_laplacian {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (∑ a, rDeriv (scalarMetricFlux g.form x u a) z a) =
      2 * Real.sqrt (realMetricFn g.form x z).det * laplacian g.form u (chartInv x z) := by
  rw [kahler_scalarMetricFlux_divergence_on g hK hu x hz,
    traceWith_inChart_eq_laplacian g.form hu x hz]

/-- Genuine local Green identity for the project's own scalar Laplacian,
 with all geometry normalizations and chart changes proved internally. -/
theorem integral_kahler_laplacian {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * (2 * Real.sqrt (realMetricFn g.form x z).det *
      laplacian g.form u (chartInv x z)) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * scalarMetricFlux g.form x u a z ∂lebesgueC n) := by
  have heq : (fun z => φ z * (2 * Real.sqrt (realMetricFn g.form x z).det *
      traceWith (hMat g.form x z) (leviC (inChart x u) z))) =
    (fun z => φ z * (2 * Real.sqrt (realMetricFn g.form x z).det *
      laplacian g.form u (chartInv x z))) := by
    funext z
    by_cases hzero : φ z = 0
    · simp only [hzero, zero_mul]
    · rw [traceWith_inChart_eq_laplacian g.form hu x (hφO (subset_closure hzero))]
  rw [← heq]
  exact integral_kahler_chart_trace g hK hu x hφ hcφ hφO

/-- The pointwise nonnegative project Laplacian implies its actual local
 distributional subharmonic inequality for every nonnegative compact test. -/
theorem integral_gradient_test_nonpos {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) (hφnonneg : ∀ z, 0 ≤ φ z)
    (hsub : ∀ z ∈ tsupport φ, 0 ≤ laplacian g.form u (chartInv x z)) :
    (∫ z, ∑ a, rDeriv φ z a * scalarMetricFlux g.form x u a z ∂lebesgueC n) ≤ 0 := by
  have hnonneg : 0 ≤ ∫ z, φ z * (2 * Real.sqrt (realMetricFn g.form x z).det *
      laplacian g.form u (chartInv x z)) ∂lebesgueC n := by
    apply integral_nonneg
    intro z
    by_cases hzero : φ z = 0
    · simp [hzero]
    · exact mul_nonneg (hφnonneg z) (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (hsub z (subset_closure hzero)))
  rw [integral_kahler_laplacian g hK hu x hφ hcφ hφO] at hnonneg
  linarith

/-- The actual inverse-metric pairing of two chart scalar differentials. -/
def chartGradientPair {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (f k : ComplexVector n → ℝ)
    (z : ComplexVector n) : ℝ :=
  ((realMetricFn h x z)⁻¹).toBilin' (fun a => rDeriv f z a) (fun b => rDeriv k z b)

theorem chartGradientPair_eq_sum {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (f k : ComplexVector n → ℝ) (z : ComplexVector n) :
    chartGradientPair h x f k z =
      ∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b * rDeriv f z a * rDeriv k z b := by
  rw [chartGradientPair, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem chartGradientPair_symm {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (f k : ComplexVector n → ℝ) (z : ComplexVector n) :
    chartGradientPair h x f k z = chartGradientPair h x k f z :=
  (Matrix.isSymm_toBilin'_iff_isSymm.mpr (realMetricFn_isSymm h x z).inv).eq _ _

/-- Energy positivity is derived from the true positive real Gram matrix. -/
theorem chartGradientPair_self_nonneg {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (f : ComplexVector n → ℝ) :
    0 ≤ chartGradientPair h x f f z := by
  have hp := (L12Aux.realMetricFn_posDef h x z hz).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun a => rDeriv f z a)
  simpa only [chartGradientPair, Matrix.toBilin'_apply', star_trivial] using hp

theorem chartGradientPair_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {f k : ComplexVector n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTarget x)) (hk : ContDiffOn ℝ ∞ k (chartTarget x)) :
    ContDiffOn ℝ ∞ (chartGradientPair g.form x f k) (chartTarget x) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hp : ContDiffOn ℝ ∞ (fun z => ∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
      rDeriv f z a * rDeriv k z b) (chartTarget x) := by
    apply ContDiffOn.sum
    intro a _
    apply ContDiffOn.sum
    intro b _
    exact ((realMetricFn_inverse_contDiffOn g x a b).mul (rDeriv_contDiffOn hO hf a)).mul
      (rDeriv_contDiffOn hO hk b)
  exact hp.congr (fun z _ => chartGradientPair_eq_sum g.form x f k z)

/-- The chart flux pairing is the actual density-weighted metric energy. -/
theorem scalarMetricFlux_pairing {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (u : M.Carrier → ℝ)
    (φ : ComplexVector n → ℝ) (z : ComplexVector n) :
    (∑ a, rDeriv φ z a * scalarMetricFlux h x u a z) =
      Real.sqrt (realMetricFn h x z).det * chartGradientPair h x φ (inChart x u) z := by
  rw [chartGradientPair_eq_sum]
  simp only [scalarMetricFlux, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The pointwise quadratic absorption used in Caccioppoli follows from
 positivity of an actual bilinear form on one explicit combined vector. -/
theorem bilin_caccioppoli_point {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) (η c : ℝ) (v w : V) :
    (1 / 2 : ℝ) * η ^ 2 * B v v - 2 * c ^ 2 * B w w ≤
      η ^ 2 * B v v + 2 * η * c * B w v := by
  have hp := hpos (η • v + (2 * c) • w)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hp
  rw [hsym w v] at hp ⊢
  nlinarith

theorem chartGradientPair_mul_left {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {f k : ComplexVector n → ℝ}
    (l : ComplexVector n → ℝ) {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hk : DifferentiableAt ℝ k z) :
    chartGradientPair h x (fun t => f t * k t) l z =
      f z * chartGradientPair h x k l z + k z * chartGradientPair h x f l z := by
  have hgrad : (fun a => rDeriv (fun t => f t * k t) z a) =
      f z • (fun a => rDeriv k z a) + k z • (fun a => rDeriv f z a) := by
    funext a
    rw [rDeriv_mul hf hk]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold chartGradientPair
  rw [hgrad]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-- A chart energy pairing vanishes outside the closed support of its
 differentiated test factor, without any regularity premise on the other factor. -/
theorem chartGradientPair_zero_of_notMem_tsupport {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (f k : ComplexVector n → ℝ)
    {z : ComplexVector n} (hz : z ∉ tsupport f) :
    chartGradientPair h x f k z = 0 := by
  unfold chartGradientPair rDeriv
  rw [fderiv_of_notMem_tsupport ℝ hz]
  change (((realMetricFn h x z)⁻¹).toBilin' (0 : RIdx n → ℝ))
    (fun b => fderiv ℝ k z (realVec b)) = 0
  simp only [map_zero, LinearMap.zero_apply]

/-- The density-weighted chart energy pairing of a compact test is
 genuinely integrable; coefficient regularity is required only on the chart. -/
theorem integrable_weighted_chartGradientPair {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {φ k w : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (hk : ContDiffOn ℝ ∞ k (chartTarget x)) (hw : ContinuousOn w (chartTarget x)) :
    Integrable (fun z => w z * chartGradientPair g.form x φ k z) (lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hpiece (a b : RIdx n) : Integrable (fun z => rDeriv φ z a *
      (w z * (realMetricFn g.form x z)⁻¹ a b * rDeriv k z b)) (lebesgueC n) :=
    integrable_compactTest_mul (lebesgueC n) hO
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hcφ.fderiv_apply ℝ (realVec a))
      ((tsupport_fderiv_apply_subset ℝ (realVec a)).trans hφO)
      ((hw.mul (realMetricFn_inverse_contDiffOn g x a b).continuousOn).mul
        (rDeriv_contDiffOn hO hk b).continuousOn)
  have hp := integrable_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ => hpiece a b))
  convert hp using 1
  funext z
  rw [chartGradientPair_eq_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The exact pointwise Caccioppoli inequality for the genuine chart metric
 and the actual square-times-function test, before integration. -/
theorem chart_caccioppoli_point {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {η f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (hη : DifferentiableAt ℝ η z) (hf : DifferentiableAt ℝ f z) :
    Real.sqrt (realMetricFn h x z).det * η z ^ 2 * chartGradientPair h x f f z ≤
      4 * (Real.sqrt (realMetricFn h x z).det * f z ^ 2 * chartGradientPair h x η η z) +
        2 * (Real.sqrt (realMetricFn h x z).det *
          chartGradientPair h x (fun t => η t * η t * f t) f z) := by
  let B := ((realMetricFn h x z)⁻¹).toBilin'
  have hs (v w : RIdx n → ℝ) : B v w = B w v :=
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (realMetricFn_isSymm h x z).inv).eq v w
  have hpos (v : RIdx n → ℝ) : 0 ≤ B v v := by
    have hp := (L12Aux.realMetricFn_posDef h x z hz).inv.posSemidef.dotProduct_mulVec_nonneg v
    simpa only [B, Matrix.toBilin'_apply', star_trivial] using hp
  have hpair : chartGradientPair h x (fun t => η t * η t * f t) f z =
      η z ^ 2 * chartGradientPair h x f f z +
        2 * η z * f z * chartGradientPair h x η f z := by
    have hsq : DifferentiableAt ℝ (fun t => η t * η t) z := hη.mul hη
    rw [chartGradientPair_mul_left (f := fun t => η t * η t) (k := f) h x f hsq hf,
      chartGradientPair_mul_left (f := η) (k := η) h x f hη hη]
    ring
  have hp := bilin_caccioppoli_point B hs hpos (η z) (f z)
    (fun a => rDeriv f z a) (fun a => rDeriv η z a)
  change (1 / 2 : ℝ) * η z ^ 2 * chartGradientPair h x f f z -
    2 * f z ^ 2 * chartGradientPair h x η η z ≤
      η z ^ 2 * chartGradientPair h x f f z +
        2 * η z * f z * chartGradientPair h x η f z at hp
  rw [← hpair] at hp
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Real.sqrt_nonneg (realMetricFn h x z).det))
  nlinarith

/-- Integrating the actual Caccioppoli pointwise bound and absorbing its
 nonpositive weak-test term requires no unproved analytic estimate. -/
theorem integral_caccioppoli_absorption {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {A R P : α → ℝ} (hA : Integrable A μ) (hR : Integrable R μ)
    (hP : Integrable P μ) (hpoint : ∀ z, A z ≤ 4 * R z + 2 * P z)
    (hweak : (∫ z, P z ∂μ) ≤ 0) :
    (∫ z, A z ∂μ) ≤ 4 * ∫ z, R z ∂μ := by
  have hm := integral_mono hA ((hR.const_mul 4).add (hP.const_mul 2)) hpoint
  change (∫ z, A z ∂μ) ≤ ∫ z, 4 * R z + 2 * P z ∂μ at hm
  rw [integral_add (hR.const_mul 4) (hP.const_mul 2), integral_const_mul, integral_const_mul] at hm
  linarith

/-- The true local Caccioppoli inequality for nonnegative project-subharmonic
 scalars, with every test-function, integrability and metric premise discharged. -/
theorem integral_chart_caccioppoli {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (hunonneg : ∀ y, 0 ≤ u y) (hsub : ∀ y, 0 ≤ laplacian g.form u y)
    (x : M.Carrier) {η : ComplexVector n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ chartTarget x) :
    (∫ z, Real.sqrt (realMetricFn g.form x z).det * η z ^ 2 *
      chartGradientPair g.form x (inChart x u) (inChart x u) z ∂lebesgueC n) ≤
        4 * ∫ z, Real.sqrt (realMetricFn g.form x z).det * (inChart x u z) ^ 2 *
          chartGradientPair g.form x η η z ∂lebesgueC n := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  let f := inChart x u
  let ρ : ComplexVector n → ℝ := fun z => Real.sqrt (realMetricFn g.form x z).det
  let φ : ComplexVector n → ℝ := fun z => η z * η z * f z
  let A : ComplexVector n → ℝ := fun z => ρ z * η z ^ 2 * chartGradientPair g.form x f f z
  let R : ComplexVector n → ℝ := fun z => ρ z * f z ^ 2 * chartGradientPair g.form x η η z
  let P : ComplexVector n → ℝ := fun z => ρ z * chartGradientPair g.form x φ f z
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hηsqO : tsupport (fun z => η z * η z) ⊆ chartTarget x :=
    tsupport_mul_subset_left.trans hηO
  have hφsupp : tsupport φ ⊆ tsupport η :=
    tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hφO : tsupport φ ⊆ chartTarget x := hφsupp.trans hηO
  have hcηsq : HasCompactSupport (fun z => η z * η z) := hcη.mul_right
  have hcφ : HasCompactSupport φ := hcηsq.mul_right
  have hφ : ContDiff ℝ ∞ φ := contDiff_mul_of_contDiffAt_tsupport (hη.mul hη)
    (fun z hz => (hu x).contDiffAt (hO.mem_nhds (hηsqO hz)))
  have hφnonneg (z : ComplexVector n) : 0 ≤ φ z :=
    mul_nonneg (mul_self_nonneg (η z)) (hunonneg (chartInv x z))
  have hρ : ContinuousOn ρ (chartTarget x) := (volumeDensity_contDiffOn g x).continuousOn
  have hAi : Integrable A (lebesgueC n) := by
    have hp := integrable_compactTest_mul (lebesgueC n) hO (hη.mul hη).continuous hcηsq hηsqO
      (hρ.mul (chartGradientPair_contDiffOn g x (hu x) (hu x)).continuousOn)
    convert hp using 1
    funext z
    dsimp [A, f]
    ring
  have hRi : Integrable R (lebesgueC n) :=
    integrable_weighted_chartGradientPair g x (hη.of_le (by simp)) hcη hηO hη.contDiffOn
      (hρ.mul ((hu x).continuousOn.pow 2))
  have hPi : Integrable P (lebesgueC n) :=
    integrable_weighted_chartGradientPair g x (hφ.of_le (by simp)) hcφ hφO (hu x) hρ
  have hpoint (z : ComplexVector n) : A z ≤ 4 * R z + 2 * P z := by
    by_cases hz : z ∈ tsupport η
    · exact chart_caccioppoli_point g.form x (hηO hz)
        (hη.differentiable (by simp) z)
        (((hu x).contDiffAt (hO.mem_nhds (hηO hz))).differentiableAt (by simp))
    · have hηz := image_eq_zero_of_notMem_tsupport hz
      have hEη := chartGradientPair_zero_of_notMem_tsupport g.form x η η hz
      have hEφ := chartGradientPair_zero_of_notMem_tsupport g.form x φ f
        (fun h => hz (hφsupp h))
      simp only [A, R, P, hηz, hEη, hEφ, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        mul_zero, zero_mul, add_zero, le_refl]
  have hweak : (∫ z, P z ∂lebesgueC n) ≤ 0 := by
    have hw := integral_gradient_test_nonpos g hK hu x (hφ.of_le (by simp)) hcφ hφO hφnonneg
      (fun z _ => hsub (chartInv x z))
    simpa only [scalarMetricFlux_pairing] using hw
  exact integral_caccioppoli_absorption (lebesgueC n) hAi hRi hPi hpoint hweak

/-- Genuine smoothness for the restricted real manifold implies exactly the
 project's chartwise real scalar smoothness. -/
theorem smoothFn_of_contMDiff_real {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ}
    (hu : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ u) : SmoothFn u := by
  letI := L12Aux.manifold_realSmooth M
  intro x
  have hcomp := hu.comp_contMDiffOn
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) x)
  have hcd := hcomp.contDiffOn
  change ContDiffOn ℝ ∞ (u ∘ (extChartAt (ComplexModel n) x).symm)
    (extChartAt (ComplexModel n) x).target
  simpa only [L12Aux.real_extChartAt_eq] using hcd

/-- Properness of the actual induced distance supplies genuine compact
 smooth cutoffs between every two concentric radii. This discharges the
 compact-domain localization internally, without a new leaf premise. -/
theorem exists_smooth_compact_cutoff {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ η : M.Carrier → ℝ, SmoothFn η ∧ HasCompactSupport η ∧
      (∀ y, η y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ y, inducedDistance g.form x y ≤ r → η y = 1) ∧
      tsupport η ⊆ distBall g.form x R := by
  letI := L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hspos : 0 < s := lt_trans hr hrs
  have hRpos : 0 < R := lt_trans hr hrR
  have hclosed : IsClosed {y : M.Carrier | inducedDistance g.form x y ≤ r} :=
    isClosed_le (L12Aux.continuous_distFrom g x) continuous_const
  have hsub : {y : M.Carrier | inducedDistance g.form x y ≤ r} ⊆ distBall g.form x s := by
    intro y hy
    exact (L12Aux.mem_distBall_iff g x y hspos).mpr (lt_of_le_of_lt hy hrs)
  obtain ⟨η, hη, hηrange, hηsupp, hηone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, ComplexVector n)) (n := (⊤ : ℕ∞))
      (L12Aux.isOpen_distBall g x s) hclosed hsub
  have hclosuresub : closure (distBall g.form x s) ⊆
      {y : M.Carrier | inducedDistance g.form x y ≤ s} :=
    closure_minimal (fun y hy => le_of_lt ((L12Aux.mem_distBall_iff g x y hspos).mp hy))
      (isClosed_le (L12Aux.continuous_distFrom g x) continuous_const)
  have hηsub : tsupport η ⊆ {y : M.Carrier | inducedDistance g.form x y ≤ s} := by
    change closure (Function.support η) ⊆ _
    rw [hηsupp]
    exact hclosuresub
  have hcη : HasCompactSupport η :=
    (L12Aux.isCompact_inducedDistance_sublevel g x s).of_isClosed_subset (isClosed_tsupport η) hηsub
  refine ⟨η, smoothFn_of_contMDiff_real hη, hcη, ?_, ?_, ?_⟩
  · intro y
    exact hηrange (Set.mem_range_self y)
  · intro y hy
    exact (hηone y).mp hy
  · intro y hy
    exact (L12Aux.mem_distBall_iff g x y hRpos).mpr (lt_of_le_of_lt (hηsub hy) hsR)

/-- The actual real Hessian product rule. -/
theorem secondFDeriv_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f k : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hk : ContDiffAt ℝ 2 k z)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun t => f t * k t)) z v w =
      f z * fderiv ℝ (fderiv ℝ k) z v w +
        k z * fderiv ℝ (fderiv ℝ f) z v w +
          fderiv ℝ f z v * fderiv ℝ k z w + fderiv ℝ k z v * fderiv ℝ f z w := by
  have hfd := hf.differentiableAt (by norm_num)
  have hkd := hk.differentiableAt (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hkdd := (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : fderiv ℝ (fun t => f t * k t) =ᶠ[𝓝 z]
      (fun t => f t • fderiv ℝ k t + k t • fderiv ℝ f t) := by
    filter_upwards [hf.eventually (by norm_num), hk.eventually (by norm_num)] with t hft hkt
    exact fderiv_fun_mul (hft.differentiableAt (by norm_num)) (hkt.differentiableAt (by norm_num))
  have h1 : DifferentiableAt ℝ (fun t => f t • fderiv ℝ k t) z := hfd.smul hkdd
  have h2 : DifferentiableAt ℝ (fun t => k t • fderiv ℝ f t) z := hkd.smul hfdd
  rw [heq.fderiv_eq, fderiv_fun_add h1 h2, fderiv_fun_smul hfd hkdd, fderiv_fun_smul hkd hfdd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- Constants satisfy the project's actual scalar smoothness predicate. -/
theorem smoothFn_const {n : ℕ} {M : ComplexManifold n} (c : ℝ) :
    SmoothFn (M := M) (fun _ => c) := fun _ => contDiffOn_const

/-- Products preserve the project's actual scalar smoothness. -/
theorem smoothFn_mul {n : ℕ} {M : ComplexManifold n} {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) : SmoothFn (fun x => u x * v x) :=
  fun x => (hu x).mul (hv x)

/-- Every natural power of a genuinely smooth scalar is genuinely smooth. -/
theorem smoothFn_pow {n : ℕ} {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (m : ℕ) : SmoothFn (fun x => u x ^ m) :=
  fun x => (hu x).pow m

/-- The computed scalar Laplacian annihilates actual constants. -/
theorem laplacian_const {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (c : ℝ) (x : M.Carrier) :
    laplacian h (fun _ => c) x = 0 := by
  have hL : levi (fun _ : M.Carrier => c) x = 0 := by
    ext a b
    unfold levi leviC leviMatrix wirt wirtBar inChart
    simp
  rw [laplacian, hL]
  simp [traceWith]

/-- Finite contraction of the actual Hessian product rule. -/
theorem principal_secondFDeriv_mul {n : ℕ} (A : Matrix (RIdx n) (RIdx n) ℝ)
    {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hk : ContDiffAt ℝ 2 k z) :
    (∑ a, ∑ b, A a b * fderiv ℝ (fderiv ℝ (fun t => f t * k t)) z (realVec a) (realVec b)) =
      f z * (∑ a, ∑ b, A a b * fderiv ℝ (fderiv ℝ k) z (realVec a) (realVec b)) +
        k z * (∑ a, ∑ b, A a b * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b)) +
          (∑ a, ∑ b, A a b * rDeriv f z a * rDeriv k z b) +
            (∑ a, ∑ b, A a b * rDeriv k z a * rDeriv f z b) := by
  calc
    _ = ∑ a, ∑ b, (f z * (A a b * fderiv ℝ (fderiv ℝ k) z (realVec a) (realVec b)) +
      k z * (A a b * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b)) +
        A a b * rDeriv f z a * rDeriv k z b + A a b * rDeriv k z a * rDeriv f z b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [secondFDeriv_mul hf hk]
      unfold rDeriv
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The product rule for the project's own scalar complex Laplacian,
 including its exact real metric energy factor. It holds for every
 Hermitian field, without a Kähler or curvature premise. -/
theorem laplacian_mul {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v)
    (x : M.Carrier) :
    laplacian h (fun y => u y * v y) x = u x * laplacian h v x + v x * laplacian h u x +
      chartGradientPair h x (inChart x u) (inChart x v) (chartPt x x) := by
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hf : ContDiffAt ℝ 2 (inChart x u) z :=
    ((hu x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hk : ContDiffAt ℝ 2 (inChart x v) z :=
    ((hv x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hp := principal_realLaplacian_eq_twice_traceWith h x hz (hf.mul hk)
  have hpU := principal_realLaplacian_eq_twice_traceWith h x hz hf
  have hpV := principal_realLaplacian_eq_twice_traceWith h x hz hk
  have hsum := principal_secondFDeriv_mul (realMetricFn h x z)⁻¹ hf hk
  have hval : chartInv x z = x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hfval : inChart x u z = u x := congrArg u hval
  have hkval : inChart x v z = v x := congrArg v hval
  rw [hp, hpV, hpU, ← chartGradientPair_eq_sum h x (inChart x u) (inChart x v) z,
    ← chartGradientPair_eq_sum h x (inChart x v) (inChart x u) z,
    chartGradientPair_symm h x (inChart x v) (inChart x u) z, hfval, hkval] at hsum
  change 2 * laplacian h (fun y => u y * v y) x =
    u x * (2 * laplacian h v x) + v x * (2 * laplacian h u x) +
      chartGradientPair h x (inChart x u) (inChart x v) z +
      chartGradientPair h x (inChart x u) (inChart x v) z at hsum
  change laplacian h (fun y => u y * v y) x = _
  linarith

/-- Actual directional differentiation of a natural scalar power. -/
theorem rDeriv_pow {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (m : ℕ) (a : RIdx n) :
    rDeriv (fun t => f t ^ m) z a = (m : ℝ) * f z ^ (m - 1) * rDeriv f z a := by
  unfold rDeriv
  rw [fderiv_fun_pow m hf]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]

/-- The true metric gradient pairing obeys the scalar power chain rule. -/
theorem chartGradientPair_pow_left {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {f : ComplexVector n → ℝ}
    (k : ComplexVector n → ℝ) {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (m : ℕ) :
    chartGradientPair h x (fun t => f t ^ m) k z =
      (m : ℝ) * f z ^ (m - 1) * chartGradientPair h x f k z := by
  have hg : (fun a => rDeriv (fun t => f t ^ m) z a) =
      ((m : ℝ) * f z ^ (m - 1)) • (fun a => rDeriv f z a) := by
    funext a
    rw [rDeriv_pow hf m a]
    rfl
  unfold chartGradientPair
  rw [hg, map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul]

/-- Every natural power of a nonnegative project-subharmonic function is
 itself project-subharmonic. Positivity uses the actual real metric inverse. -/
theorem laplacian_pow_nonneg {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (hunonneg : ∀ x, 0 ≤ u x) (hsub : ∀ x, 0 ≤ laplacian h u x) (m : ℕ) (x : M.Carrier) :
    0 ≤ laplacian h (fun y => u y ^ m) x := by
  induction m with
  | zero => simp only [pow_zero, laplacian_const, le_refl]
  | succ m hm =>
    simp only [pow_succ]
    rw [laplacian_mul h (smoothFn_pow hu m) hu x]
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (pow_nonneg (hunonneg x) _) (hsub x))
        (mul_nonneg (hunonneg x) hm)
    · have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
      have hf : DifferentiableAt ℝ (inChart x u) (chartPt x x) :=
        (contDiffAt_inChart hu x hz).differentiableAt (by simp)
      change 0 ≤ chartGradientPair h x (fun t => inChart x u t ^ m) (inChart x u) (chartPt x x)
      rw [chartGradientPair_pow_left h x (inChart x u) hf m]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m)
        (pow_nonneg (hunonneg (chartInv x (chartPt x x))) _))
        (chartGradientPair_self_nonneg h x hz (inChart x u))

/-- Caccioppoli applies to every actual natural power of the original
 nonnegative subharmonic scalar, with no new subharmonicity hypothesis. -/
theorem integral_chart_caccioppoli_pow {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (hunonneg : ∀ y, 0 ≤ u y) (hsub : ∀ y, 0 ≤ laplacian g.form u y)
    (m : ℕ) (x : M.Carrier) {η : ComplexVector n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ chartTarget x) :
    (∫ z, Real.sqrt (realMetricFn g.form x z).det * η z ^ 2 *
      chartGradientPair g.form x (inChart x (fun y => u y ^ m))
        (inChart x (fun y => u y ^ m)) z ∂lebesgueC n) ≤
      4 * ∫ z, Real.sqrt (realMetricFn g.form x z).det * (inChart x (fun y => u y ^ m) z) ^ 2 *
        chartGradientPair g.form x η η z ∂lebesgueC n :=
  integral_chart_caccioppoli g hK (smoothFn_pow hu m)
    (fun y => pow_nonneg (hunonneg y) m) (laplacian_pow_nonneg g.form hu hunonneg hsub m)
    x hη hcη hηO

/-- Project smoothness implies smoothness for the genuine restricted real
 manifold, so the two scalar smoothness notions are identified internally. -/
theorem contMDiff_real_of_smoothFn {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) :
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ u := by
  letI := L12Aux.manifold_realSmooth M
  intro x
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  apply ContDiffAt.contMDiffAt
  have hc := contDiffAt_inChart hu x (mem_extChartAt_target x)
  change ContDiffAt ℝ ∞ (u ∘ (extChartAt (ComplexModel n) x).symm)
    (extChartAt (ComplexModel n) x x) at hc
  simpa only [L12Aux.real_extChartAt_eq] using hc

/-- A model-valued chart test, transported to its chart source and extended
 by its actual zero value to the rest of the manifold. -/
def chartPushforwardZero {n : ℕ} {M : ComplexManifold n} {F : Type*} [Zero F]
    (x : M.Carrier) (φ : ComplexVector n → F) (y : M.Carrier) : F :=
  @ite F (y ∈ (extChartAt (ComplexModel n) x).source) (Classical.propDecidable _)
    (φ (chartPt x y)) 0

/-- The genuine chart zero extension recovers its model test on the chart
 target; no claim is made about arbitrary off-target inverse-chart values. -/
theorem chartPushforwardZero_chartInv {n : ℕ} {M : ComplexManifold n}
    {F : Type*} [Zero F] (x : M.Carrier) (φ : ComplexVector n → F)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartPushforwardZero x φ (chartInv x z) = φ z := by
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz
  have hp : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  simp only [chartPushforwardZero, if_pos hy, hp]

/-- A genuine compact chart test into any real normed vector space has a
 compactly supported globally smooth zero extension on the manifold.
 The support lies in the actual chart source. -/
theorem chartPushforwardZero_properties {n : ℕ} {M : ComplexManifold n}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : M.Carrier) {φ : ComplexVector n → F}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    HasCompactSupport (chartPushforwardZero x φ) ∧
      ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞ (chartPushforwardZero x φ) ∧
        tsupport (chartPushforwardZero x φ) ⊆ (extChartAt (ComplexModel n) x).source := by
  letI := L12Aux.manifold_realSmooth M
  let Ξ := chartPushforwardZero x φ
  let K := chartInv x '' tsupport φ
  have hc : IsCompact (tsupport φ) := hcφ
  have hK : IsCompact K := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono hφO)
  have hKs : K ⊆ (extChartAt (ComplexModel n) x).source := by
    rintro y ⟨z, hz, rfl⟩
    exact (extChartAt (ComplexModel n) x).map_target (hφO hz)
  have hsupp : Function.support Ξ ⊆ K := by
    intro y hy
    change Ξ y ≠ 0 at hy
    by_cases hys : y ∈ (extChartAt (ComplexModel n) x).source
    · have hφnz : φ (chartPt x y) ≠ 0 := by
        simpa only [Ξ, chartPushforwardZero, if_pos hys] using hy
      exact ⟨chartPt x y, subset_closure hφnz, (extChartAt (ComplexModel n) x).left_inv hys⟩
    · have hzero : Ξ y = 0 := by simp only [Ξ, chartPushforwardZero, if_neg hys]
      exact False.elim (hy hzero)
  have htsupp : tsupport Ξ ⊆ K := closure_minimal hsupp hK.isClosed
  have hΞs : tsupport Ξ ⊆ (extChartAt (ComplexModel n) x).source := htsupp.trans hKs
  have hcΞ : HasCompactSupport Ξ := hK.of_isClosed_subset (isClosed_tsupport Ξ) htsupp
  refine ⟨hcΞ, ?_, hΞs⟩
  apply contMDiff_of_tsupport
  intro y hy
  have hys := hΞs hy
  have hchart := contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := ∞)
    (x := x) (x' := y) (by simpa only [extChartAt_source] using hys)
  have hcomp := hφ.contMDiff.contMDiffAt.comp y hchart
  have hcomp' : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞
      (fun p => φ (chartPt x p)) y := by
    change ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞
      (φ ∘ extChartAt (ComplexModel n) x) y
    simpa only [L12Aux.real_extChartAt_eq] using hcomp
  have heq : Ξ =ᶠ[𝓝 y] (fun p => φ (chartPt x p)) := by
    filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hys] with p hp
    simp only [Ξ, chartPushforwardZero, if_pos hp]
  exact hcomp'.congr_of_eventuallyEq heq

/-- Scalar chart tests therefore give actual project-smooth compact tests. -/
theorem smoothFn_chartPushforwardZero {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    SmoothFn (chartPushforwardZero x φ) :=
  smoothFn_of_contMDiff_real (chartPushforwardZero_properties x hφ hcφ hφO).2.1

/-- Every compact set has an actual finite smooth nonnegative partition
 subordinate to genuine chart sources. The weights are real smooth functions. -/
theorem exists_finite_smooth_partition {n : ℕ} {M : ComplexManifold n}
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ s : Finset M.Carrier, ∃ p : s → M.Carrier → ℝ,
      (∀ i, SmoothFn (p i)) ∧ (∀ i y, 0 ≤ p i y) ∧
        (∀ i, tsupport (p i) ⊆ (extChartAt (ComplexModel n) (i : M.Carrier)).source) ∧
          (∀ y ∈ K, ∑ i, p i y = 1) := by
  classical
  letI := L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : M.Carrier => (extChartAt (ComplexModel n) x).source)
    (fun x => isOpen_extChartAt_source x)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, mem_extChartAt_source y⟩)
  have hcover : K ⊆ ⋃ i : s, (extChartAt (ComplexModel n) (i : M.Carrier)).source := by
    intro y hy
    rcases Set.mem_iUnion.mp (hs hy) with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxs, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hxs⟩, hxy⟩
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexVector n)) hK.isClosed
    (fun i : s => (extChartAt (ComplexModel n) (i : M.Carrier)).source)
    (fun i => isOpen_extChartAt_source (i : M.Carrier)) hcover
  refine ⟨s, fun i => p i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact smoothFn_of_contMDiff_real (p i).contMDiff
  · exact p.nonneg
  · exact hp
  · intro y hy
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hy

/-- Finite smooth-partition globalization rests on actual integrable weighted
 pieces. Integrability of the unweighted function is derived in the proof. -/
theorem integral_finite_partition {α F ι : Type*} [MeasurableSpace α] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure α) (w : ι → α → ℝ) (f : α → F)
    (hpieces : ∀ i, Integrable (fun x => w i x • f x) μ)
    (hsum : ∀ x ∈ Function.support f, ∑ i, w i x = 1) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = ∑ i, ∫ x, w i x • f x ∂μ := by
  have heq : (fun x => ∑ i, w i x • f x) = f := by
    funext x
    by_cases hzero : f x = 0
    · simp only [hzero, smul_zero, Finset.sum_const_zero]
    · rw [← Finset.sum_smul, hsum x hzero, one_smul]
  have hi := integrable_finsetSum Finset.univ (fun i _ => hpieces i)
  refine ⟨hi.congr (ae_of_all _ (fun x => congrFun heq x)), ?_⟩
  calc
    (∫ x, f x ∂μ) = ∫ x, ∑ i, w i x • f x ∂μ :=
      congrArg (fun q : α → F => ∫ x, q x ∂μ) heq.symm
    _ = ∑ i, ∫ x, w i x • f x ∂μ := integral_finsetSum Finset.univ (fun i _ => hpieces i)

/-- A manifold function supported in one chart source, pulled back to that
 chart target and extended by zero to the full model space. -/
def chartPullbackZero {n : ℕ} {M : ComplexManifold n} {F : Type*} [Zero F]
    (x : M.Carrier) (ψ : M.Carrier → F) (z : ComplexVector n) : F :=
  @ite F (z ∈ chartTarget x) (Classical.propDecidable _) (ψ (chartInv x z)) 0

/-- Recovery of the actual manifold test on its chart source. -/
theorem chartPullbackZero_chartPt {n : ℕ} {M : ComplexManifold n}
    {F : Type*} [Zero F] (x : M.Carrier) (ψ : M.Carrier → F)
    {y : M.Carrier} (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    chartPullbackZero x ψ (chartPt x y) = ψ y := by
  have hz : chartPt x y ∈ chartTarget x := (extChartAt (ComplexModel n) x).map_source hy
  have hp : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
  simp only [chartPullbackZero, if_pos hz, hp]

/-- A genuinely smooth compactly supported manifold test in one chart has
 a genuine compactly supported smooth model-space zero pullback. This holds
 for any real normed target, including fixed alternating-tensor spaces. -/
theorem chartPullbackZero_properties {n : ℕ} {M : ComplexManifold n}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : M.Carrier) {ψ : M.Carrier → F}
    (hψ : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞ ψ)
    (hcψ : HasCompactSupport ψ)
    (hψO : tsupport ψ ⊆ (extChartAt (ComplexModel n) x).source) :
    HasCompactSupport (chartPullbackZero x ψ) ∧ ContDiff ℝ ∞ (chartPullbackZero x ψ) ∧
      tsupport (chartPullbackZero x ψ) ⊆ chartTarget x := by
  letI := L12Aux.manifold_realSmooth M
  let Φ := chartPullbackZero x ψ
  let K := chartPt x '' tsupport ψ
  have hc : IsCompact (tsupport ψ) := hcψ
  have hK : IsCompact K := hc.image_of_continuousOn
    ((continuousOn_extChartAt (I := ComplexModel n) x).mono hψO)
  have hKt : K ⊆ chartTarget x := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt (ComplexModel n) x).map_source (hψO hy)
  have hsupp : Function.support Φ ⊆ K := by
    intro z hz
    change Φ z ≠ 0 at hz
    by_cases hzt : z ∈ chartTarget x
    · have hψnz : ψ (chartInv x z) ≠ 0 := by
        simpa only [Φ, chartPullbackZero, if_pos hzt] using hz
      exact ⟨chartInv x z, subset_closure hψnz, (extChartAt (ComplexModel n) x).right_inv hzt⟩
    · have hzero : Φ z = 0 := by simp only [Φ, chartPullbackZero, if_neg hzt]
      exact False.elim (hz hzero)
  have htsupp : tsupport Φ ⊆ K := closure_minimal hsupp hK.isClosed
  have hΦt : tsupport Φ ⊆ chartTarget x := htsupp.trans hKt
  have hcΦ : HasCompactSupport Φ := hK.of_isClosed_subset (isClosed_tsupport Φ) htsupp
  refine ⟨hcΦ, ?_, hΦt⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport Φ
  · have hzt := hΦt hz
    have hzr : z ∈ (extChartAt 𝓘(ℝ, ComplexVector n) x).target := by
      rwa [L12Aux.real_extChartAt_eq]
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) x).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, ComplexVector n)) x).mem_nhds hzr)
    have hcomp := hψ.contMDiffAt.comp z hi
    have hcd : ContDiffAt ℝ ∞ (fun w => ψ (chartInv x w)) z := by
      change ContDiffAt ℝ ∞ (ψ ∘ (extChartAt (ComplexModel n) x).symm) z
      simpa only [L12Aux.real_extChartAt_eq] using hcomp.contDiffAt
    have heq : Φ =ᶠ[𝓝 z] (fun w => ψ (chartInv x w)) := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hzt] with w hw
      have hwt : w ∈ chartTarget x := hw
      simp only [Φ, chartPullbackZero, if_pos hwt]
    exact hcd.congr_of_eventuallyEq heq
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hz)

/-- Project-smooth scalar tests satisfy the preceding genuine model-space
 smoothness and compact-support conclusions. -/
theorem chartPullbackZero_smoothFn {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (hcψ : HasCompactSupport ψ)
    (hψO : tsupport ψ ⊆ (extChartAt (ComplexModel n) x).source) :
    HasCompactSupport (chartPullbackZero x ψ) ∧ ContDiff ℝ ∞ (chartPullbackZero x ψ) ∧
      tsupport (chartPullbackZero x ψ) ⊆ chartTarget x :=
  chartPullbackZero_properties x (contMDiff_real_of_smoothFn hψ) hcψ hψO

/-- The scalar Laplacian product rule in any fixed chart, derived using
 the actual Hessian rule and the proved scalar chart invariance. -/
theorem laplacian_mul_in_chart {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    laplacian h (fun y => u y * v y) (chartInv x z) =
      u (chartInv x z) * laplacian h v (chartInv x z) +
        v (chartInv x z) * laplacian h u (chartInv x z) +
          chartGradientPair h x (inChart x u) (inChart x v) z := by
  have hf : ContDiffAt ℝ 2 (inChart x u) z := (contDiffAt_inChart hu x hz).of_le (by simp)
  have hk : ContDiffAt ℝ 2 (inChart x v) z := (contDiffAt_inChart hv x hz).of_le (by simp)
  have hp := (principal_realLaplacian_eq_twice_traceWith h x hz (hf.mul hk)).trans
    (congrArg (fun q => 2 * q) (traceWith_inChart_eq_laplacian h (smoothFn_mul hu hv) x hz))
  have hpU := (principal_realLaplacian_eq_twice_traceWith h x hz hf).trans
    (congrArg (fun q => 2 * q) (traceWith_inChart_eq_laplacian h hu x hz))
  have hpV := (principal_realLaplacian_eq_twice_traceWith h x hz hk).trans
    (congrArg (fun q => 2 * q) (traceWith_inChart_eq_laplacian h hv x hz))
  have hsum := principal_secondFDeriv_mul (realMetricFn h x z)⁻¹ hf hk
  rw [hp, hpV, hpU, ← chartGradientPair_eq_sum h x (inChart x u) (inChart x v) z,
    ← chartGradientPair_eq_sum h x (inChart x v) (inChart x u) z,
    chartGradientPair_symm h x (inChart x v) (inChart x u) z] at hsum
  change 2 * laplacian h (fun y => u y * v y) (chartInv x z) =
    u (chartInv x z) * (2 * laplacian h v (chartInv x z)) +
      v (chartInv x z) * (2 * laplacian h u (chartInv x z)) +
        chartGradientPair h x (inChart x u) (inChart x v) z +
        chartGradientPair h x (inChart x u) (inChart x v) z at hsum
  linarith

/-- The actual scalar metric pairing, computed in the centered chart.
 Its independence of that chart is proved below. -/
def scalarGradientPair {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (u v : M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  chartGradientPair h x (inChart x u) (inChart x v) (chartPt x x)

theorem scalarGradientPair_laplacian_identity {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v)
    (x : M.Carrier) :
    scalarGradientPair h u v x = laplacian h (fun y => u y * v y) x -
      u x * laplacian h v x - v x * laplacian h u x := by
  have hp := laplacian_mul h hu hv x
  unfold scalarGradientPair
  linarith

/-- The physical scalar metric pairing is exactly its actual coordinate
 expression throughout every chart target. -/
theorem scalarGradientPair_eq_chart {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    scalarGradientPair h u v (chartInv x z) = chartGradientPair h x (inChart x u) (inChart x v) z := by
  rw [scalarGradientPair_laplacian_identity h hu hv]
  have hp := laplacian_mul_in_chart h hu hv x hz
  linarith

theorem scalarGradientPair_symm {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (u v : M.Carrier → ℝ) (x : M.Carrier) :
    scalarGradientPair h u v x = scalarGradientPair h v u x :=
  chartGradientPair_symm h x (inChart x u) (inChart x v) (chartPt x x)

theorem scalarGradientPair_self_nonneg {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (u : M.Carrier → ℝ) (x : M.Carrier) :
    0 ≤ scalarGradientPair h u u x :=
  chartGradientPair_self_nonneg h x (mem_extChartAt_target x) (inChart x u)

theorem smoothFn_sub {n : ℕ} {M : ComplexManifold n} {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) : SmoothFn (fun x => u x - v x) :=
  fun x => (hu x).sub (hv x)

/-- The intrinsic scalar metric pairing is smooth for the actual smooth
 metric and smooth scalar inputs. -/
theorem smoothFn_scalarGradientPair {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v) :
    SmoothFn (scalarGradientPair g.form u v) := by
  have hp := smoothFn_sub
    (smoothFn_sub (smoothFn_laplacian g (smoothFn_mul hu hv))
      (smoothFn_mul hu (smoothFn_laplacian g hv)))
    (smoothFn_mul hv (smoothFn_laplacian g hu))
  have heq : scalarGradientPair g.form u v =
      (fun y => laplacian g.form (fun x => u x * v x) y -
        u y * laplacian g.form v y - v y * laplacian g.form u y) :=
    funext (scalarGradientPair_laplacian_identity g.form hu hv)
  rw [heq]
  exact hp

/-- Actual inverse-chart continuity transports every scalar germ at the
 manifold point to the corresponding centered coordinate germ. -/
theorem inChart_eventuallyEq {n : ℕ} {M : ComplexManifold n} {α : Type*}
    {u v : M.Carrier → α} {x : M.Carrier} (heq : u =ᶠ[𝓝 x] v) :
    inChart x u =ᶠ[𝓝 (chartPt x x)] inChart x v := by
  have hval : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hc := continuousAt_extChartAt_symm (I := ComplexModel n) x
  change Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 (chartInv x (chartPt x x))) at hc
  rw [hval] at hc
  exact hc.eventually heq

/-- The physical energy is local in its first differentiated scalar. -/
theorem scalarGradientPair_zero_of_notMem_tsupport {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (u v : M.Carrier → ℝ) {x : M.Carrier} (hx : x ∉ tsupport u) :
    scalarGradientPair h u v x = 0 := by
  have heq : u =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hx
  have hh := (inChart_eventuallyEq heq).fderiv_eq (𝕜 := ℝ)
  have hd : fderiv ℝ (inChart x u) (chartPt x x) = 0 :=
    hh.trans (fderiv_const_apply (0 : ℝ))
  unfold scalarGradientPair chartGradientPair rDeriv
  rw [hd]
  change (((realMetricFn h x (chartPt x x))⁻¹).toBilin' (0 : RIdx n → ℝ))
    (fun b => fderiv ℝ (inChart x v) (chartPt x x) (realVec b)) = 0
  simp only [map_zero, LinearMap.zero_apply]

theorem scalarGradientPair_tsupport_subset_left {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (u v : M.Carrier → ℝ) :
    tsupport (scalarGradientPair h u v) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  change scalarGradientPair h u v x ≠ 0 at hx
  by_contra hxu
  exact hx (scalarGradientPair_zero_of_notMem_tsupport h u v hxu)

theorem scalarGradientPair_hasCompactSupport {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (u v : M.Carrier → ℝ) (hcu : HasCompactSupport u) :
    HasCompactSupport (scalarGradientPair h u v) :=
  (show IsCompact (tsupport u) from hcu).of_isClosed_subset
    (isClosed_tsupport _) (scalarGradientPair_tsupport_subset_left h u v)

/-- Every actual compactly supported project-smooth scalar is integrable
 for the leaf's exact Riemannian measure. -/
theorem smoothFn_integrable_compact {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hcu : HasCompactSupport u) : Integrable u μ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  exact (continuous_of_smoothFn hu).integrable_of_hasCompactSupport hcu

theorem scalarGradientPair_integrable {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v) (hcu : HasCompactSupport u) :
    Integrable (scalarGradientPair g.form u v) μ :=
  smoothFn_integrable_compact g μ hμ (smoothFn_scalarGradientPair g hu hv)
    (scalarGradientPair_hasCompactSupport g.form u v hcu)

/-- Properness and the actual chart volume imply finite volume for every
 positive-radius ball of the original induced distance. -/
theorem riemannianVolume_distBall_lt_top {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) : μ (distBall g.form x r) < ⊤ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  have hsub : distBall g.form x r ⊆ {y : M.Carrier | inducedDistance g.form x y ≤ r} := by
    intro y hy
    exact ((L12Aux.mem_distBall_iff g x y hr).mp hy).le
  exact lt_of_le_of_lt (measure_mono hsub) (L12Aux.isCompact_inducedDistance_sublevel g x r).measure_lt_top

/-- Exact full integral transport for a measurable scalar supported in one
 actual chart source. Both zero extensions are justified pointwise. -/
theorem integral_chart_volume_of_tsupport {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (f : M.Carrier → ℝ) (hf : Measurable f)
    (hfs : tsupport f ⊆ (extChartAt (ComplexModel n) x).source) :
    (∫ y, f y ∂μ) = ∫ z, Real.sqrt (realMetricFn g.form x z).det * chartPullbackZero x f z ∂lebesgueC n := by
  have hs : (∫ y in (extChartAt (ComplexModel n) x).source, f y ∂μ) = ∫ y, f y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      image_eq_zero_of_notMem_tsupport (fun h => hy (hfs h))
  calc
    (∫ y, f y ∂μ) = ∫ y in (extChartAt (ComplexModel n) x).source, f y ∂μ := hs.symm
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * f (chartInv x z) ∂lebesgueC n :=
      integral_chart_volume g μ hμ x f hf
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * chartPullbackZero x f z ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      have hzt : z ∈ chartTarget x := hz
      simp only [chartPullbackZero, if_pos hzt]
    _ = ∫ z, Real.sqrt (realMetricFn g.form x z).det * chartPullbackZero x f z ∂lebesgueC n := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp only [chartPullbackZero, if_neg hz, mul_zero]

/-- The zero pullback of a scalar product keeps the supported first factor. -/
theorem chartPullbackZero_mul {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (f k : M.Carrier → ℝ) (z : ComplexVector n) :
    chartPullbackZero x (fun y => f y * k y) z = chartPullbackZero x f z * k (chartInv x z) := by
  by_cases hz : z ∈ chartTarget x <;> simp [chartPullbackZero, hz]

/-- On the open chart target, zero pullback and ordinary chart expression
 have exactly the same actual differential in the metric pairing. -/
theorem chartGradientPair_pullbackZero {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (ψ : M.Carrier → ℝ)
    (k : ComplexVector n → ℝ) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartGradientPair h x (chartPullbackZero x ψ) k z = chartGradientPair h x (inChart x ψ) k z := by
  classical
  have heq : chartPullbackZero x ψ =ᶠ[𝓝 z] inChart x ψ := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    have hwt : w ∈ chartTarget x := hw
    change (if w ∈ chartTarget x then ψ (chartInv x w) else 0) = ψ (chartInv x w)
    exact if_pos hwt
  unfold chartGradientPair rDeriv
  rw [heq.fderiv_eq (𝕜 := ℝ)]

/-- Finite sums preserve genuine project scalar smoothness. -/
theorem smoothFn_sum {n : ℕ} {M : ComplexManifold n} {ι : Type*} [Fintype ι]
    (f : ι → M.Carrier → ℝ) (hf : ∀ i, SmoothFn (f i)) :
    SmoothFn (fun y => ∑ i, f i y) := fun x => ContDiffOn.sum (fun i _ => hf i x)

/-- The actual physical energy pairing is linear in finite sums of smooth
 scalars in its first differentiated argument. -/
theorem scalarGradientPair_sum_left {n : ℕ} {M : ComplexManifold n} {ι : Type*} [Fintype ι]
    (h : HermitianField M) (f : ι → M.Carrier → ℝ) (hf : ∀ i, SmoothFn (f i))
    (u : M.Carrier → ℝ) (x : M.Carrier) :
    scalarGradientPair h (fun y => ∑ i, f i y) u x = ∑ i, scalarGradientPair h (f i) u x := by
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hd (i : ι) : DifferentiableAt ℝ (inChart x (f i)) z :=
    (contDiffAt_inChart (hf i) x hz).differentiableAt (by simp)
  have hg : (fun a => rDeriv (inChart x (fun y => ∑ i, f i y)) z a) =
      ∑ i, (fun a => rDeriv (inChart x (f i)) z a) := by
    funext a
    change rDeriv (fun w => ∑ i, inChart x (f i) w) z a = _
    rw [rDeriv_sum (fun i => inChart x (f i)) hd a]
    simp only [Finset.sum_apply]
  unfold scalarGradientPair chartGradientPair
  rw [hg, map_sum]
  simp only [LinearMap.sum_apply]
  rfl

/-- Full Green identity for an actual compact scalar test supported in one
 chart source, expressed in the root's own volume and intrinsic scalar
 energy. Both integrability conclusions are proved internally. -/
theorem integral_scalar_green_in_chart {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u ψ : M.Carrier → ℝ}
    (hu : SmoothFn u) (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ)
    (x : M.Carrier) (hψs : tsupport ψ ⊆ (extChartAt (ComplexModel n) x).source) :
    Integrable (fun y => ψ y * laplacian g.form u y) μ ∧
      Integrable (scalarGradientPair g.form ψ u) μ ∧
        (∫ y, ψ y * laplacian g.form u y ∂μ) =
          -(1 / 2 : ℝ) * ∫ y, scalarGradientPair g.form ψ u y ∂μ := by
  let Φ := chartPullbackZero x ψ
  let ρ : ComplexVector n → ℝ := fun z => Real.sqrt (realMetricFn g.form x z).det
  have hΦ : HasCompactSupport Φ ∧ ContDiff ℝ ∞ Φ ∧ tsupport Φ ⊆ chartTarget x :=
    chartPullbackZero_smoothFn x hψ hcψ hψs
  have hcI : HasCompactSupport (fun y => ψ y * laplacian g.form u y) := hcψ.mul_right
  have hIint : Integrable (fun y => ψ y * laplacian g.form u y) μ :=
    smoothFn_integrable_compact g μ hμ (smoothFn_mul hψ (smoothFn_laplacian g hu)) hcI
  have hEint : Integrable (scalarGradientPair g.form ψ u) μ :=
    scalarGradientPair_integrable g μ hμ hψ hu hcψ
  have hI : (∫ y, ψ y * laplacian g.form u y ∂μ) =
      ∫ z, ρ z * Φ z * laplacian g.form u (chartInv x z) ∂lebesgueC n := by
    calc
      _ = ∫ z, ρ z * chartPullbackZero x (fun y => ψ y * laplacian g.form u y) z ∂lebesgueC n :=
        integral_chart_volume_of_tsupport g μ hμ x _
          (continuous_of_smoothFn (smoothFn_mul hψ (smoothFn_laplacian g hu))).measurable
          (tsupport_mul_subset_left.trans hψs)
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by
          change ρ z * chartPullbackZero x (fun y => ψ y * laplacian g.form u y) z =
            ρ z * Φ z * laplacian g.form u (chartInv x z)
          rw [chartPullbackZero_mul x ψ (laplacian g.form u) z]
          change ρ z * (Φ z * laplacian g.form u (chartInv x z)) =
            ρ z * Φ z * laplacian g.form u (chartInv x z)
          ring)
  have hE : (∫ y, scalarGradientPair g.form ψ u y ∂μ) =
      ∫ z, ρ z * chartGradientPair g.form x Φ (inChart x u) z ∂lebesgueC n := by
    calc
      _ = ∫ z, ρ z * chartPullbackZero x (scalarGradientPair g.form ψ u) z ∂lebesgueC n :=
        integral_chart_volume_of_tsupport g μ hμ x _
          (continuous_of_smoothFn (smoothFn_scalarGradientPair g hψ hu)).measurable
          ((scalarGradientPair_tsupport_subset_left g.form ψ u).trans hψs)
      _ = _ := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        change ρ z * chartPullbackZero x (scalarGradientPair g.form ψ u) z =
          ρ z * chartGradientPair g.form x Φ (inChart x u) z
        by_cases hz : z ∈ chartTarget x
        · have heval : chartPullbackZero x (scalarGradientPair g.form ψ u) z =
              scalarGradientPair g.form ψ u (chartInv x z) := by
            simp only [chartPullbackZero, if_pos hz]
          rw [heval, scalarGradientPair_eq_chart g.form hψ hu x hz,
            chartGradientPair_pullbackZero g.form x ψ (inChart x u) hz]
        · have heval : chartPullbackZero x (scalarGradientPair g.form ψ u) z = 0 := by
            simp only [chartPullbackZero, if_neg hz]
          have hnot : z ∉ tsupport Φ := fun h => hz (hΦ.2.2 h)
          have hzero := chartGradientPair_zero_of_notMem_tsupport g.form x Φ (inChart x u) hnot
          rw [heval, hzero]
  have hG := integral_kahler_laplacian g hK hu x (hΦ.2.1.of_le (by simp)) hΦ.1 hΦ.2.2
  have hLeft : (∫ z, Φ z * (2 * ρ z * laplacian g.form u (chartInv x z)) ∂lebesgueC n) =
      2 * ∫ y, ψ y * laplacian g.form u y ∂μ := by
    calc
      _ = ∫ z, 2 * (ρ z * Φ z * laplacian g.form u (chartInv x z)) ∂lebesgueC n := by
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring)
      _ = 2 * ∫ z, ρ z * Φ z * laplacian g.form u (chartInv x z) ∂lebesgueC n := integral_const_mul _ _
      _ = _ := congrArg (fun q => 2 * q) hI.symm
  have hRight : (∫ z, ∑ a, rDeriv Φ z a * scalarMetricFlux g.form x u a z ∂lebesgueC n) =
      ∫ y, scalarGradientPair g.form ψ u y ∂μ := by
    calc
      _ = ∫ z, ρ z * chartGradientPair g.form x Φ (inChart x u) z ∂lebesgueC n := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => scalarMetricFlux_pairing g.form x u Φ z)
      _ = _ := hE.symm
  change (∫ z, Φ z * (2 * ρ z * laplacian g.form u (chartInv x z)) ∂lebesgueC n) =
    -(∫ z, ∑ a, rDeriv Φ z a * scalarMetricFlux g.form x u a z ∂lebesgueC n) at hG
  rw [hLeft, hRight] at hG
  exact ⟨hIint, hEint, by linarith⟩

/-- The actual global scalar Green identity for every smooth compact test.
 The finite chart partition, model tests, chart volume transport and both
 integrability claims are all constructed inside this proof. -/
theorem integral_scalar_green {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u ψ : M.Carrier → ℝ}
    (hu : SmoothFn u) (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun y => ψ y * laplacian g.form u y) μ ∧
      Integrable (scalarGradientPair g.form ψ u) μ ∧
        (∫ y, ψ y * laplacian g.form u y ∂μ) =
          -(1 / 2 : ℝ) * ∫ y, scalarGradientPair g.form ψ u y ∂μ := by
  classical
  obtain ⟨s, p, hp, _, hps, hsum⟩ :=
    exists_finite_smooth_partition (show IsCompact (tsupport ψ) from hcψ)
  let η : s → M.Carrier → ℝ := fun i y => p i y * ψ y
  have hη (i : s) : SmoothFn (η i) := smoothFn_mul (hp i) hψ
  have hcη (i : s) : HasCompactSupport (η i) := hcψ.mul_left
  have hηs (i : s) : tsupport (η i) ⊆ (extChartAt (ComplexModel n) (i : M.Carrier)).source :=
    tsupport_mul_subset_left.trans (hps i)
  have hloc (i : s) := integral_scalar_green_in_chart g hK μ hμ hu (hη i) (hcη i)
    (i : M.Carrier) (hηs i)
  have hsumFn : (fun y => ∑ i, η i y) = ψ := by
    funext y
    change (∑ i, p i y * ψ y) = ψ y
    rw [← Finset.sum_mul]
    by_cases hzero : ψ y = 0
    · simp only [hzero, mul_zero]
    · rw [hsum y (subset_closure hzero), one_mul]
  have hpieces (i : s) : Integrable (fun y => p i y • (ψ y * laplacian g.form u y)) μ := by
    convert (hloc i).1 using 1
    funext y
    simp only [smul_eq_mul, η]
    ring
  have hsumI : ∀ y ∈ Function.support (fun y => ψ y * laplacian g.form u y), ∑ i, p i y = 1 := by
    intro y hy
    have hψnz : ψ y ≠ 0 := by
      intro hzero
      apply hy
      simp only [hzero, zero_mul]
    exact hsum y (subset_closure hψnz)
  have hIformal := integral_finite_partition μ p (fun y => ψ y * laplacian g.form u y) hpieces hsumI
  have hIeq : (∫ y, ψ y * laplacian g.form u y ∂μ) =
      ∑ i, ∫ y, η i y * laplacian g.form u y ∂μ := by
    calc
      _ = ∑ i, ∫ y, p i y • (ψ y * laplacian g.form u y) ∂μ := hIformal.2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by simp only [smul_eq_mul, η]; ring)
  have hsumE : (fun y => ∑ i, scalarGradientPair g.form (η i) u y) = scalarGradientPair g.form ψ u := by
    funext y
    rw [← scalarGradientPair_sum_left g.form η hη u y]
    exact congrArg (fun q : M.Carrier → ℝ => scalarGradientPair g.form q u y) hsumFn
  have hEeq : (∫ y, scalarGradientPair g.form ψ u y ∂μ) =
      ∑ i, ∫ y, scalarGradientPair g.form (η i) u y ∂μ := by
    calc
      _ = ∫ y, ∑ i, scalarGradientPair g.form (η i) u y ∂μ :=
        congrArg (fun q : M.Carrier → ℝ => ∫ y, q y ∂μ) hsumE.symm
      _ = _ := integral_finsetSum Finset.univ (fun i _ => (hloc i).2.1)
  refine ⟨hIformal.1, scalarGradientPair_integrable g μ hμ hψ hu hcψ, ?_⟩
  calc
    _ = ∑ i, ∫ y, η i y * laplacian g.form u y ∂μ := hIeq
    _ = ∑ i, (-(1 / 2 : ℝ)) * ∫ y, scalarGradientPair g.form (η i) u y ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hloc i).2.2
    _ = (-(1 / 2 : ℝ)) * ∑ i, ∫ y, scalarGradientPair g.form (η i) u y ∂μ :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (fun q => (-(1 / 2 : ℝ)) * q) hEeq.symm

/-- Sharp support information for the normed-target chart pushforward.
 Smoothness of the model function is unnecessary for this compact-image fact. -/
theorem chartPushforwardZero_tsupport_subset {n : ℕ} {M : ComplexManifold n}
    {F : Type*} [Zero F] (x : M.Carrier) {φ : ComplexVector n → F}
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x) :
    tsupport (chartPushforwardZero x φ) ⊆ chartInv x '' tsupport φ := by
  let Ξ := chartPushforwardZero x φ
  let K := chartInv x '' tsupport φ
  have hc : IsCompact (tsupport φ) := hcφ
  have hK : IsCompact K := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono hφO)
  have hsupp : Function.support Ξ ⊆ K := by
    intro y hy
    change Ξ y ≠ 0 at hy
    by_cases hys : y ∈ (extChartAt (ComplexModel n) x).source
    · have hφnz : φ (chartPt x y) ≠ 0 := by
        simpa only [Ξ, chartPushforwardZero, if_pos hys] using hy
      exact ⟨chartPt x y, subset_closure hφnz, (extChartAt (ComplexModel n) x).left_inv hys⟩
    · exact False.elim (hy (by simp only [Ξ, chartPushforwardZero, if_neg hys]))
  exact closure_minimal hsupp hK.isClosed

/-- The reverse chart zero extension also has its precise compact image
 as a support bound, for any target type with an actual zero. -/
theorem chartPullbackZero_tsupport_subset {n : ℕ} {M : ComplexManifold n}
    {F : Type*} [Zero F] (x : M.Carrier) {ψ : M.Carrier → F}
    (hcψ : HasCompactSupport ψ)
    (hψO : tsupport ψ ⊆ (extChartAt (ComplexModel n) x).source) :
    tsupport (chartPullbackZero x ψ) ⊆ chartPt x '' tsupport ψ := by
  let Φ := chartPullbackZero x ψ
  let K := chartPt x '' tsupport ψ
  have hc : IsCompact (tsupport ψ) := hcψ
  have hK : IsCompact K := hc.image_of_continuousOn
    ((continuousOn_extChartAt (I := ComplexModel n) x).mono hψO)
  have hsupp : Function.support Φ ⊆ K := by
    intro z hz
    change Φ z ≠ 0 at hz
    by_cases hzt : z ∈ chartTarget x
    · have hψnz : ψ (chartInv x z) ≠ 0 := by
        simpa only [Φ, chartPullbackZero, if_pos hzt] using hz
      exact ⟨chartInv x z, subset_closure hψnz, (extChartAt (ComplexModel n) x).right_inv hzt⟩
    · exact False.elim (hz (by simp only [Φ, chartPullbackZero, if_neg hzt]))
  exact closure_minimal hsupp hK.isClosed

/-- The original pointwise project subharmonicity gives the actual global
 weak inequality for every nonnegative smooth compact scalar test. -/
theorem integral_scalar_gradient_test_nonpos {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u ψ : M.Carrier → ℝ}
    (hu : SmoothFn u) (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ)
    (hψnonneg : ∀ y, 0 ≤ ψ y) (hsub : ∀ y ∈ tsupport ψ, 0 ≤ laplacian g.form u y) :
    (∫ y, scalarGradientPair g.form ψ u y ∂μ) ≤ 0 := by
  have hG := (integral_scalar_green g hK μ hμ hu hψ hcψ).2.2
  have hn : 0 ≤ ∫ y, ψ y * laplacian g.form u y ∂μ := by
    apply integral_nonneg
    intro y
    by_cases hzero : ψ y = 0
    · simp [hzero]
    · exact mul_nonneg (hψnonneg y) (hsub y (subset_closure hzero))
  rw [hG] at hn
  linarith

/-- Pointwise Caccioppoli for the intrinsic physical energy. Its positive
 density is cancelled using the true real metric determinant. -/
theorem scalar_caccioppoli_point {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u η : M.Carrier → ℝ} (hu : SmoothFn u) (hη : SmoothFn η)
    (x : M.Carrier) :
    η x ^ 2 * scalarGradientPair h u u x ≤
      4 * (u x ^ 2 * scalarGradientPair h η η x) +
        2 * scalarGradientPair h (fun y => η y * η y * u y) u x := by
  let ρ := Real.sqrt (realMetricFn h x (chartPt x x)).det
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hfη := (contDiffAt_inChart hη x hz).differentiableAt (by simp)
  have hfu := (contDiffAt_inChart hu x hz).differentiableAt (by simp)
  have hp := chart_caccioppoli_point h x hz hfη hfu
  have hval : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hηval : inChart x η (chartPt x x) = η x := congrArg η hval
  have huval : inChart x u (chartPt x x) = u x := congrArg u hval
  rw [hηval, huval] at hp
  change ρ * η x ^ 2 * scalarGradientPair h u u x ≤
    4 * (ρ * u x ^ 2 * scalarGradientPair h η η x) +
      2 * (ρ * scalarGradientPair h (fun y => η y * η y * u y) u x) at hp
  have hm : ρ * (η x ^ 2 * scalarGradientPair h u u x) ≤
      ρ * (4 * (u x ^ 2 * scalarGradientPair h η η x) +
        2 * scalarGradientPair h (fun y => η y * η y * u y) u x) := by
    convert hp using 1 <;> ring
  exact le_of_mul_le_mul_left hm (L12Aux.volumeDensity_pos h x (chartPt x x) hz)

/-- Global Caccioppoli in the root's genuine measure, for every actual
 smooth compact cutoff. All support, integrability and weak-test premises
 are discharged, including the square-times-subharmonic test. -/
theorem integral_scalar_caccioppoli {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u η : M.Carrier → ℝ}
    (hu : SmoothFn u) (hunonneg : ∀ y, 0 ≤ u y) (hsub : ∀ y, 0 ≤ laplacian g.form u y)
    (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    (∫ y, η y ^ 2 * scalarGradientPair g.form u u y ∂μ) ≤
      4 * ∫ y, u y ^ 2 * scalarGradientPair g.form η η y ∂μ := by
  let φ : M.Carrier → ℝ := fun y => η y * η y * u y
  have hφ : SmoothFn φ := smoothFn_mul (smoothFn_mul hη hη) hu
  have hcηsq : HasCompactSupport (fun y => η y * η y) := hcη.mul_right
  have hcφ : HasCompactSupport φ := hcηsq.mul_right
  have hφnonneg (y : M.Carrier) : 0 ≤ φ y := mul_nonneg (mul_self_nonneg (η y)) (hunonneg y)
  have hweak : (∫ y, scalarGradientPair g.form φ u y ∂μ) ≤ 0 :=
    integral_scalar_gradient_test_nonpos g hK μ hμ hu hφ hcφ hφnonneg (fun y _ => hsub y)
  have hcη2 : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [pow_two] using hcηsq
  have hA : Integrable (fun y => η y ^ 2 * scalarGradientPair g.form u u y) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hη 2) (smoothFn_scalarGradientPair g hu hu)) hcη2.mul_right
  have hR : Integrable (fun y => u y ^ 2 * scalarGradientPair g.form η η y) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hu 2) (smoothFn_scalarGradientPair g hη hη))
      (scalarGradientPair_hasCompactSupport g.form η η hcη).mul_left
  have hP : Integrable (scalarGradientPair g.form φ u) μ := scalarGradientPair_integrable g μ hμ hφ hu hcφ
  exact integral_caccioppoli_absorption μ hA hR hP (scalar_caccioppoli_point g.form hu hη) hweak

/-- The exact Riemannian chart law forces positive volume on every
 nonempty open subset of the manifold. -/
theorem riemannianVolume_open_pos {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {s : Set M.Carrier} (hs : IsOpen s) (hne : s.Nonempty) : 0 < μ s := by
  classical
  obtain ⟨a, ha⟩ := hne
  let U := s ∩ (chartAt (ComplexVector n) a).source
  let V := chartPt a '' U
  have hU : IsOpen U := hs.inter (chartAt (ComplexVector n) a).open_source
  have hV : IsOpen V := by
    change IsOpen ((chartAt (ComplexVector n) a) '' U)
    exact (chartAt (ComplexVector n) a).isOpen_image_of_subset_source hU Set.inter_subset_right
  have hVne : V.Nonempty := ⟨chartPt a a, a, ⟨ha, mem_chart_source _ _⟩, rfl⟩
  have hVt : V ⊆ chartTarget a := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt (ComplexModel n) a).map_source (by simpa only [extChartAt_source] using hy.2)
  let d : ComplexVector n → ℝ≥0∞ := (chartTarget a).piecewise
    (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det)) (fun _ => 0)
  have hd : Measurable d :=
    (ENNReal.continuous_ofReal.comp_continuousOn (volumeDensity_continuousOn g a)).measurable_piecewise
      continuousOn_const (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hsupport : Function.support d ∩ V = V := by
    apply Set.Subset.antisymm Set.inter_subset_right
    intro z hz
    refine ⟨?_, hz⟩
    change d z ≠ 0
    simp only [d, Set.piecewise, if_pos (hVt hz)]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (L12Aux.volumeDensity_pos g.form a z (hVt hz)))
  have hLeb : 0 < (lebesgueC n) V := by
    rw [lebesgueC_eq_volume]
    exact hV.measure_pos volume hVne
  have hJ : 0 < ∫⁻ z in V, d z ∂lebesgueC n :=
    (setLIntegral_pos_iff hd).mpr (by rw [hsupport]; exact hLeb)
  have heq : (∫⁻ z in V, d z ∂lebesgueC n) =
      ∫⁻ z in V, ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det) ∂lebesgueC n := by
    apply setLIntegral_congr_fun hV.measurableSet
    intro z hz
    simp only [d, Set.piecewise, if_pos (hVt hz)]
  rw [heq] at hJ
  have hUpos : 0 < μ U := by
    rw [hμ a U hU.measurableSet Set.inter_subset_right]
    exact hJ
  exact lt_of_lt_of_le hUpos (measure_mono Set.inter_subset_left)

/-- The original volume measure has full topological support, proved from
 its actual positive chart density rather than assumed as a measure field. -/
theorem riemannianVolume_isOpenPosMeasure {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    μ.IsOpenPosMeasure := by
  constructor
  intro U hU hne
  exact ne_of_gt (riemannianVolume_open_pos g μ hμ hU hne)

/-- Every original positive-radius ball has strictly positive actual volume. -/
theorem riemannianVolume_distBall_pos {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) : 0 < μ (distBall g.form x r) := by
  apply riemannianVolume_open_pos g μ hμ (L12Aux.isOpen_distBall g x r)
  refine ⟨x, ?_⟩
  rw [L12Aux.mem_distBall_iff g x x hr, g.induced_distance_eq_zero.mpr rfl]
  exact hr

/-- The genuine second Fréchet derivative of a scalar function is the
 usual second derivative, multiplied by its two scalar directions. -/
theorem secondFDeriv_scalar_apply {F : ℝ → ℝ} {t : ℝ}
    (hF : ContDiffAt ℝ 2 F t) (a b : ℝ) :
    fderiv ℝ (fderiv ℝ F) t a b = a * b * deriv (deriv F) t := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) t :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : deriv (deriv F) t = fderiv ℝ (fderiv ℝ F) t 1 1 := by
    change fderiv ℝ (fun y => (fderiv ℝ F y) 1) t 1 = _
    rw [fderiv_clm_apply hd (differentiableAt_const (1 : ℝ))]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  rw [he]
  have ha := (fderiv ℝ (fderiv ℝ F) t).map_smul a (1 : ℝ)
  have hb := (fderiv ℝ F t).map_smul b (1 : ℝ)
  have hb' := ((fderiv ℝ (fderiv ℝ F) t) 1).map_smul b (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at ha hb hb'
  rw [ha]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hb']
  ring

/-- Scalar composition contracts against the actual inverse metric with
 the genuine first and second derivatives of its outer function. -/
theorem principal_secondFDeriv_scalar_comp {n : ℕ}
    (A : Matrix (RIdx n) (RIdx n) ℝ) {f : ComplexVector n → ℝ}
    {F : ℝ → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (f z)) :
    (∑ a, ∑ b, A a b * fderiv ℝ (fderiv ℝ (F ∘ f)) z (realVec a) (realVec b)) =
      deriv F (f z) *
        (∑ a, ∑ b, A a b * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b)) +
      deriv (deriv F) (f z) * (∑ a, ∑ b, A a b * rDeriv f z a * rDeriv f z b) := by
  calc
    _ = ∑ a, ∑ b,
        (deriv F (f z) * (A a b * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b)) +
        deriv (deriv F) (f z) * (A a b * rDeriv f z a * rDeriv f z b)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [secondFDeriv_comp hf hF, secondFDeriv_scalar_apply hF, fderiv_eq_deriv_mul]
      unfold rDeriv
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The project's actual complex Laplacian obeys the scalar C² chain
 rule, including its factor one-half on the physical real metric energy. -/
theorem laplacian_scalar_comp {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (F : ℝ → ℝ) (x : M.Carrier) (hF : ContDiffAt ℝ 2 F (u x)) :
    laplacian h (fun y => F (u y)) x = deriv F (u x) * laplacian h u x +
      (1 / 2 : ℝ) * deriv (deriv F) (u x) * scalarGradientPair h u u x := by
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hf : ContDiffAt ℝ 2 (inChart x u) z :=
    ((hu x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hval : inChart x u z = u x :=
    congrArg u ((extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x))
  have hF' : ContDiffAt ℝ 2 F (inChart x u z) := by rw [hval]; exact hF
  have hp := principal_realLaplacian_eq_twice_traceWith h x hz (hF'.comp z hf)
  have hpu := principal_realLaplacian_eq_twice_traceWith h x hz hf
  have hsum := principal_secondFDeriv_scalar_comp (realMetricFn h x z)⁻¹ hf hF'
  rw [hp, hpu, ← chartGradientPair_eq_sum h x (inChart x u) (inChart x u) z, hval] at hsum
  change 2 * laplacian h (fun y => F (u y)) x =
    deriv F (u x) * (2 * laplacian h u x) +
      deriv (deriv F) (u x) * scalarGradientPair h u u x at hsum
  linarith

/-- Smooth increasing convex scalar composition preserves actual
 pointwise subharmonicity, proved using the physical energy positivity. -/
theorem laplacian_scalar_comp_nonneg {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (hsub : ∀ x, 0 ≤ laplacian h u x) (F : ℝ → ℝ)
    (hF : ∀ x, ContDiffAt ℝ 2 F (u x))
    (hF' : ∀ x, 0 ≤ deriv F (u x))
    (hF'' : ∀ x, 0 ≤ deriv (deriv F) (u x)) :
    ∀ x, 0 ≤ laplacian h (fun y => F (u y)) x := by
  intro x
  rw [laplacian_scalar_comp h hu F x (hF x)]
  exact add_nonneg (mul_nonneg (hF' x) (hsub x))
    (mul_nonneg (mul_nonneg (by norm_num) (hF'' x)) (scalarGradientPair_self_nonneg h u x))

/-- A nonvanishing smooth scalar admits every real power as a genuine
 smooth scalar in all actual manifold charts. -/
theorem smoothFn_rpow {n : ℕ} {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (hne : ∀ x, u x ≠ 0) (p : ℝ) :
    SmoothFn (fun x => u x ^ p) := by
  intro x
  exact (hu x).rpow_const_of_ne (fun z _ => hne (chartInv x z))

/-- The actual second derivative of a real power at a nonzero scalar. -/
theorem secondDeriv_rpow {t : ℝ} (ht : t ≠ 0) (p : ℝ) :
    deriv (deriv (fun y : ℝ => y ^ p)) t = p * (p - 1) * t ^ (p - 2) := by
  rw [Real.deriv_rpow_const' p]
  have hd := ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht)).const_mul p).deriv
  convert hd using 1 <;> ring

/-- Exact positive real-power formula for the project's scalar Laplacian,
 with its physical metric energy and all actual derivative factors. -/
theorem laplacian_rpow {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (p : ℝ) (x : M.Carrier) (hne : u x ≠ 0) :
    laplacian h (fun y => u y ^ p) x =
      p * u x ^ (p - 1) * laplacian h u x +
        (1 / 2 : ℝ) * (p * (p - 1) * u x ^ (p - 2)) * scalarGradientPair h u u x := by
  rw [laplacian_scalar_comp h hu (fun t : ℝ => t ^ p) x
    (Real.contDiffAt_rpow_const_of_ne hne), Real.deriv_rpow_const, secondDeriv_rpow hne]

/-- Every positive real power with exponent at least one preserves the
 root's actual pointwise subharmonicity. -/
theorem laplacian_rpow_nonneg {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (hpos : ∀ x, 0 < u x) (hsub : ∀ x, 0 ≤ laplacian h u x)
    {p : ℝ} (hp : 1 ≤ p) : ∀ x, 0 ≤ laplacian h (fun y => u y ^ p) x := by
  intro x
  rw [laplacian_rpow h hu p x (ne_of_gt (hpos x))]
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  exact add_nonneg
    (mul_nonneg (mul_nonneg hp0 (Real.rpow_nonneg (hpos x).le _)) (hsub x))
    (mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp)) (Real.rpow_nonneg (hpos x).le _)))
      (scalarGradientPair_self_nonneg h u x))

/-- The original global Caccioppoli identity applies to every real Moser
 power of a positive smooth subharmonic function, with no extra weak or
 integrability premises. -/
theorem integral_scalar_caccioppoli_rpow {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u η : M.Carrier → ℝ}
    (hu : SmoothFn u) (hpos : ∀ x, 0 < u x) (hsub : ∀ x, 0 ≤ laplacian g.form u x)
    {p : ℝ} (hp : 1 ≤ p) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    (∫ y, η y ^ 2 * scalarGradientPair g.form (fun x => u x ^ p) (fun x => u x ^ p) y ∂μ) ≤
      4 * ∫ y, (u y ^ p) ^ 2 * scalarGradientPair g.form η η y ∂μ := by
  exact integral_scalar_caccioppoli g hK μ hμ (smoothFn_rpow hu (fun x => ne_of_gt (hpos x)) p)
    (fun x => Real.rpow_nonneg (hpos x).le p) (laplacian_rpow_nonneg g.form hu hpos hsub hp) hη hcη

/-- Smooth scalar integrals on every original positive-radius ball are
 genuine finite Bochner integrals, using the actual compact distance balls. -/
theorem smoothFn_integrableOn_distBall {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) {r : ℝ} (hr : 0 < r) :
    IntegrableOn u (distBall g.form x r) μ := by
  apply (smoothFn_integrableOn_compact g μ hμ hu
    (L12Aux.isCompact_inducedDistance_sublevel g x r)).mono_set
  intro y hy
  exact ((L12Aux.mem_distBall_iff g x y hr).mp hy).le

/-- The derived full support of actual volume converts a continuous
 almost-everywhere bound on any open set into an everywhere bound there. -/
theorem smoothFn_le_of_ae_le_open {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) {U : Set M.Carrier}
    (hU : IsOpen U) {c : ℝ} (hae : ∀ᵐ x ∂μ.restrict U, u x ≤ c) :
    ∀ x ∈ U, u x ≤ c := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have he : (fun x => min (u x) c) =ᵐ[μ.restrict U] u :=
    hae.mono (fun x hx => min_eq_left hx)
  have huc := continuous_of_smoothFn hu
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq he hU
    (huc.min continuous_const).continuousOn huc.continuousOn
  intro x hx
  exact min_eq_left_iff.mp (heq hx)

/-- A positive bilinear quadratic form bounds the square of a sum by
 twice the sum of the two squares. -/
theorem bilin_add_self_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hpos : ∀ v, 0 ≤ B v v) (v w : V) :
    B (v + w) (v + w) ≤ 2 * (B v v + B w w) := by
  have hp := hpos (v - w)
  simp only [map_sub, LinearMap.sub_apply] at hp
  simp only [map_add, LinearMap.add_apply]
  linarith

/-- The true chart metric energy obeys the product estimate at every
 actual chart point. Positivity comes from the genuine inverse Gram matrix. -/
theorem chartGradientPair_product_self_le {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {f k : ComplexVector n → ℝ}
    {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (hf : DifferentiableAt ℝ f z) (hk : DifferentiableAt ℝ k z) :
    chartGradientPair h x (fun t => f t * k t) (fun t => f t * k t) z ≤
      2 * (f z ^ 2 * chartGradientPair h x k k z + k z ^ 2 * chartGradientPair h x f f z) := by
  let B := ((realMetricFn h x z)⁻¹).toBilin'
  have hpos (v : RIdx n → ℝ) : 0 ≤ B v v := by
    have hp := (L12Aux.realMetricFn_posDef h x z hz).inv.posSemidef.dotProduct_mulVec_nonneg v
    simpa only [B, Matrix.toBilin'_apply', star_trivial] using hp
  have hgrad : (fun a => rDeriv (fun t => f t * k t) z a) =
      f z • (fun a => rDeriv k z a) + k z • (fun a => rDeriv f z a) := by
    funext a
    rw [rDeriv_mul hf hk]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hp := bilin_add_self_le B hpos
    (f z • (fun a => rDeriv k z a)) (k z • (fun a => rDeriv f z a))
  unfold chartGradientPair
  rw [hgrad]
  convert hp using 1 <;>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two] <;> ring

/-- The physical scalar energy of an actual product has the standard
 cutoff bound, valid for every original Hermitian field. -/
theorem scalarGradientPair_product_self_le {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u η : M.Carrier → ℝ} (hu : SmoothFn u) (hη : SmoothFn η)
    (x : M.Carrier) :
    scalarGradientPair h (fun y => η y * u y) (fun y => η y * u y) x ≤
      2 * (η x ^ 2 * scalarGradientPair h u u x + u x ^ 2 * scalarGradientPair h η η x) := by
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hfu : DifferentiableAt ℝ (inChart x u) z :=
    ((hu x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hfη : DifferentiableAt ℝ (inChart x η) z :=
    ((hη x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hp := chartGradientPair_product_self_le h x hz hfη hfu
  have hval : chartInv x z = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  change scalarGradientPair h (fun y => η y * u y) (fun y => η y * u y) x ≤
    2 * (η (chartInv x z) ^ 2 * scalarGradientPair h u u x +
      u (chartInv x z) ^ 2 * scalarGradientPair h η η x) at hp
  simpa only [hval] using hp

/-- Combining actual global Caccioppoli with the physical product rule
 bounds the total energy of a compact cutoff times a subharmonic scalar.
 All three integrability statements are derived from genuine smoothness
 and compact support inside the proof. -/
theorem integral_scalar_cutoff_energy {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u η : M.Carrier → ℝ}
    (hu : SmoothFn u) (hunonneg : ∀ y, 0 ≤ u y) (hsub : ∀ y, 0 ≤ laplacian g.form u y)
    (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    (∫ y, scalarGradientPair g.form (fun x => η x * u x) (fun x => η x * u x) y ∂μ) ≤
      10 * ∫ y, u y ^ 2 * scalarGradientPair g.form η η y ∂μ := by
  have hcη2 : HasCompactSupport (fun y => η y ^ 2) := by
    have hcsq : HasCompactSupport (fun y => η y * η y) := hcη.mul_right
    simpa only [pow_two] using hcsq
  have hA : Integrable (fun y => η y ^ 2 * scalarGradientPair g.form u u y) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hη 2) (smoothFn_scalarGradientPair g hu hu)) hcη2.mul_right
  have hR : Integrable (fun y => u y ^ 2 * scalarGradientPair g.form η η y) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hu 2) (smoothFn_scalarGradientPair g hη hη))
      (scalarGradientPair_hasCompactSupport g.form η η hcη).mul_left
  have hw := smoothFn_mul hη hu
  have hE : Integrable (scalarGradientPair g.form (fun y => η y * u y) (fun y => η y * u y)) μ :=
    scalarGradientPair_integrable g μ hμ hw hw hcη.mul_right
  have hp := integral_mono hE ((hA.add hR).const_mul 2)
    (scalarGradientPair_product_self_le g.form hu hη)
  rw [integral_const_mul] at hp
  change (∫ y, scalarGradientPair g.form (fun x => η x * u x) (fun x => η x * u x) y ∂μ) ≤
    2 * ∫ y, (η y ^ 2 * scalarGradientPair g.form u u y +
      u y ^ 2 * scalarGradientPair g.form η η y) ∂μ at hp
  rw [integral_add hA hR] at hp
  have hC := integral_scalar_caccioppoli g hK μ hμ hu hunonneg hsub hη hcη
  linarith

/-- Adding a genuine scalar constant does not change the project's actual
 Laplacian; this supplies the positive epsilon regularization for real powers. -/
theorem laplacian_add_const {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u) (c : ℝ) (x : M.Carrier) :
    laplacian h (fun y => u y + c) x = laplacian h u x := by
  have hD : deriv (fun t : ℝ => t + c) = fun _ => 1 :=
    funext (fun t => ((hasDerivAt_id t).add_const c).deriv)
  rw [laplacian_scalar_comp h hu (fun t : ℝ => t + c) x
    (contDiffAt_id.add contDiffAt_const), hD]
  simp

/-- A complex covector on the real inverse-chart frame has real entries
 Re ξ_i and minus Im ξ_i, as required for the real dual metric. -/
theorem covector_realVec_re {n : ℕ} {M : ComplexManifold n}
    (x y : M.Carrier) (ξ : Covector n) (a : RIdx n) :
    (ξ (chartVec x y (realVec a))).re =
      if a.2 = 0 then (ξ (chartVec x y (stdVec a.1))).re
        else -(ξ (chartVec x y (stdVec a.1))).im := by
  by_cases ha : a.2 = 0
  · simp [realVec, stdVec, chartVec_smul, ha]
  · simp only [realVec, if_neg ha, chartVec_smul, stdVec]
    change (ξ (Complex.I • (show ComplexVector n from
      chartVec x y (EuclideanSpace.single a.1 1)))).re =
        -(ξ (show ComplexVector n from chartVec x y (EuclideanSpace.single a.1 1))).im
    rw [ξ.map_smul]
    simp [smul_eq_mul]

/-- The transpose in the complex cotangent norm is exactly the sign change
 in the imaginary entries of its real covector coordinates. -/
theorem complex_dual_quadratic_realification {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) :
    (star ξ ⬝ᵥ (A.transpose *ᵥ ξ)).re =
      ∑ a : RIdx n, ∑ b : RIdx n, realRepresentation A a b *
        (if a.2 = 0 then (ξ a.1).re else -(ξ a.1).im) *
        (if b.2 = 0 then (ξ b.1).re else -(ξ b.1).im) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.star_apply,
    Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, realRepresentation_apply]
  norm_num
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The paper's complete dual-norm normalization holds for every actual
 Hermitian field and every genuine cotangent vector, with factor two. -/
theorem paperDualNormNormalization {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) : PaperDualNormNormalization h := by
  intro x ξ
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hInv : ((realMetricFn h x (chartPt x x))⁻¹ : Matrix (RIdx n) (RIdx n) ℝ) =
      (1 / 2 : ℝ) • realRepresentation ((hMat h x (chartPt x x))⁻¹) :=
    realMetricFn_inverse h x hz
  change dualNorm h x ξ = 2 * ∑ a, ∑ b,
    ((realMetricFn h x (chartPt x x))⁻¹ : Matrix (RIdx n) (RIdx n) ℝ) a b *
      (ξ (chartVec x x (realVec a))).re * (ξ (chartVec x x (realVec b))).re
  rw [hInv]
  unfold dualNorm dualNormMat
  rw [complex_dual_quadratic_realification]
  simp only [Matrix.smul_apply, smul_eq_mul, covectorCoords, WithLp.ofLp_toLp,
    covector_realVec_re, gMat]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The squared ordinary dual operator norm in any finite real basis is
 contraction with the inverse of its genuine inner-product Gram matrix. -/
theorem dual_opNorm_sq_inverse_gram {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : Module.Basis ι ℝ V) (L : V →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ a, ∑ c, (Matrix.gram ℝ b)⁻¹ a c * L (b a) * L (b c) := by
  classical
  letI : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
  let v := (InnerProductSpace.toDual ℝ V).symm L
  let G : Matrix ι ι ℝ := Matrix.gram ℝ b
  let d : ι → ℝ := fun a => L (b a)
  have hv (w : V) : inner ℝ v w = L w := InnerProductSpace.toDual_symm_apply
  have hG : G.det ≠ 0 := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  have hcoeff : G *ᵥ (b.repr v) = d := by
    funext a
    change (∑ c, inner ℝ (b a) (b c) * b.repr v c) = L (b a)
    calc
      _ = inner ℝ (b a) v := by
        conv_rhs => rw [← b.sum_repr v]
        simp only [inner_sum, inner_smul_right]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = L (b a) := by rw [real_inner_comm]; exact hv (b a)
  have hcoord : b.repr v = G⁻¹ *ᵥ d := by
    calc
      _ = (1 : Matrix ι ι ℝ) *ᵥ (b.repr v) := by rw [Matrix.one_mulVec]
      _ = (G⁻¹ * G) *ᵥ (b.repr v) := by rw [Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hG)]
      _ = G⁻¹ *ᵥ d := by rw [← Matrix.mulVec_mulVec, hcoeff]
  calc
    ‖L‖ ^ 2 = ‖v‖ ^ 2 := by rw [(InnerProductSpace.toDual ℝ V).symm.norm_map]
    _ = L v := by rw [← real_inner_self_eq_norm_sq, hv]
    _ = ∑ a, b.repr v a * L (b a) := by
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ a, ∑ c, G⁻¹ a c * d c * d a := by
      rw [hcoord]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, d]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      change G⁻¹ a c * d c * d a = G⁻¹ a c * d a * d c
      ring

/-- The genuine centered inverse-chart frame is an algebraic real
 isomorphism onto the actual real tangent fibre. -/
def centeredRealFrameEquiv {n : ℕ} {M : ComplexManifold n} (x : M.Carrier) :
    ComplexVector n ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x where
  toLinearMap := ((L12Aux.realTangentEquiv x).symm.toLinearMap).comp
    ((mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x).symm (chartPt x x)).restrictScalars ℝ).toLinearMap
  invFun v := tangentCoords x x (L12Aux.realTangentEquiv x v)
  left_inv v := by
    change tangentCoords x x (L12Aux.realTangentEquiv x
      ((L12Aux.realTangentEquiv x).symm (chartVec x x v))) = v
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) v
  right_inv v := by
    change (L12Aux.realTangentEquiv x).symm
      (chartVec x x (tangentCoords x x (L12Aux.realTangentEquiv x v))) = v
    rw [L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x)]
    exact ContinuousLinearEquiv.symm_apply_apply _ _

theorem centeredRealFrameEquiv_apply {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (v : ComplexVector n) :
    centeredRealFrameEquiv x v = (L12Aux.realTangentEquiv x).symm (chartVec x x v) := rfl

/-- The actual real inverse-chart vectors form a basis of the tangent
 fibre, independent of any later choice of a norm on that fibre. -/
def centeredRealFrameBasis {n : ℕ} {M : ComplexManifold n} (x : M.Carrier) :
    Module.Basis (RIdx n) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
  (complexVector_realOrthonormalBasis n).toBasis.map (centeredRealFrameEquiv x)

theorem centeredRealFrameBasis_apply {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (a : RIdx n) :
    centeredRealFrameBasis x a = (L12Aux.realTangentEquiv x).symm (chartVec x x (realVec a)) := by
  simp only [centeredRealFrameBasis, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
    complexVector_realOrthonormalBasis_apply, centeredRealFrameEquiv_apply]

/-- The Gram matrix of the actual real tangent basis is precisely the
 original real metric calculator, after the metric norm is installed. -/
theorem centeredRealFrameBasis_gram {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
    letI := L12Aux.underlyingRealTangentInnerProductSpace h x
    Matrix.gram ℝ (centeredRealFrameBasis x) = realMetricFn h x (chartPt x x) := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
  letI := L12Aux.underlyingRealTangentInnerProductSpace h x
  ext a b
  simp only [Matrix.gram_apply, centeredRealFrameBasis_apply]
  change (L12Aux.underlyingRealRiemannianMetric h).inner x _ _ = _
  rw [L12Aux.underlyingRealRiemannianMetric_inner, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  have hval : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  unfold realMetricFn
  rw [hval]

/-- Squared ordinary metric-dual norm in the actual centered tangent frame.
 No smoothness or curvature assumption is needed for this pointwise identity. -/
theorem realDual_opNorm_sq {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier)
    (L : letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
      letI := L12Aux.underlyingRealTangentInnerProductSpace h x
      TangentSpace 𝓘(ℝ, ComplexVector n) x →L[ℝ] ℝ) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
    letI := L12Aux.underlyingRealTangentInnerProductSpace h x
    ‖L‖ ^ 2 = ∑ a, ∑ b,
      (realMetricFn h x (chartPt x x))⁻¹ a b *
        L ((L12Aux.realTangentEquiv x).symm (chartVec x x (realVec a))) *
        L ((L12Aux.realTangentEquiv x).symm (chartVec x x (realVec b))) := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
  letI := L12Aux.underlyingRealTangentInnerProductSpace h x
  have hp := dual_opNorm_sq_inverse_gram (centeredRealFrameBasis x) L
  rw [centeredRealFrameBasis_gram h x] at hp
  simpa only [centeredRealFrameBasis_apply] using hp

/-- Actual vector-valued differentiation along the real inverse-chart
 differential is ordinary differentiation of the same chart expression. -/
theorem scalar_mvfderiv_realChartVec {n : ℕ} {M : ComplexManifold n}
    (u : M.Carrier → ℝ) (x : M.Carrier) (z v : ComplexVector n)
    (hz : z ∈ chartTarget x)
    (hu : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) u (chartInv x z)) :
    mvfderiv 𝓘(ℝ, ComplexVector n) u (chartInv x z) (L12Aux.realChartVec x z v) =
      fderiv ℝ (inChart x u) z v := by
  letI := L12Aux.manifold_realSmooth M
  have hz' : z ∈ (extChartAt 𝓘(ℝ, ComplexVector n) x).target := hz
  have hinv : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
      (chartInv x) z := by
    have hs := contMDiffWithinAt_extChartAt_symm_range
      (I := 𝓘(ℝ, ComplexVector n)) (n := ∞) x hz'
    rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hs
    exact hs.mdifferentiableAt (by simp)
  have hchain := mvfderiv_comp_apply z hu hinv
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)
  rw [mvfderiv_eq_fderiv] at hchain
  exact hchain.symm

/-- The actual scalar differential on the genuine centered real frame is
 the root's original coordinate directional derivative. -/
theorem scalar_mvfderiv_centeredFrame {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) (v : ComplexVector n) :
    mvfderiv 𝓘(ℝ, ComplexVector n) u x (centeredRealFrameEquiv x v) =
      fderiv ℝ (inChart x u) (chartPt x x) v := by
  letI := L12Aux.manifold_realSmooth M
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hval : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hmd : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) u (chartInv x (chartPt x x)) := by
    rw [hval]
    exact (contMDiff_real_of_smoothFn hu x).mdifferentiableAt (by simp)
  have hp := scalar_mvfderiv_realChartVec u x (chartPt x x) v hz hmd
  have hv : L12Aux.realChartVec x (chartPt x x) v =
      (L12Aux.realTangentEquiv (chartInv x (chartPt x x))).symm
        (chartVec x (chartInv x (chartPt x x)) v) := by
    apply (L12Aux.realTangentEquiv (chartInv x (chartPt x x))).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact L12Aux.realTangentEquiv_realChartVec x (chartPt x x) v hz
  rw [hv] at hp
  change (fun y => mvfderiv 𝓘(ℝ, ComplexVector n) u y
    ((L12Aux.realTangentEquiv y).symm (chartVec x y v))) (chartInv x (chartPt x x)) = _ at hp
  rw [hval] at hp
  exact hp

/-- The physical scalar energy is the squared ordinary operator norm of
 the actual manifold differential, for the same real metric `2 Re h`.
 This identifies the quantitative cutoff norm with the energy used in Moser. -/
theorem scalarGradientPair_eq_realDifferential_opNorm_sq {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => L12Aux.underlyingRealTangentNormedAddCommGroup h y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => L12Aux.underlyingRealTangentInnerProductSpace h y
    scalarGradientPair h u u x =
      ‖(NormedSpace.fromTangentSpace (u x)).toContinuousLinearMap ∘L
        mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) u x‖ ^ 2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => L12Aux.underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => L12Aux.underlyingRealTangentInnerProductSpace h y
  change scalarGradientPair h u u x = ‖mvfderiv 𝓘(ℝ, ComplexVector n) u x‖ ^ 2
  rw [realDual_opNorm_sq h x (mvfderiv 𝓘(ℝ, ComplexVector n) u x)]
  unfold scalarGradientPair
  rw [chartGradientPair_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← centeredRealFrameEquiv_apply, ← centeredRealFrameEquiv_apply,
    scalar_mvfderiv_centeredFrame hu, scalar_mvfderiv_centeredFrame hu]
  rfl

/-- Real coordinates of the actual `(1,0)` differential are one-half
 the coordinates of the genuine real differential, with cotangent signs. -/
theorem wirt_ofReal_real_coordinates {n : ℕ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : DifferentiableAt ℝ f z) (a : RIdx n) :
    (if a.2 = 0 then (wirt (fun t => (f t : ℂ)) z (stdVec a.1)).re
      else -(wirt (fun t => (f t : ℂ)) z (stdVec a.1)).im) =
        (1 / 2 : ℝ) * rDeriv f z a := by
  have hd : fderiv ℝ (fun t => (f t : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ f z) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ f) z = _
    rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hf]
    simp
  rw [wirt, hd]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  by_cases ha : a.2 = 0 <;>
    simp [ha, rDeriv, realVec, stdVec, Complex.mul_re, Complex.mul_im]

/-- The paper's actual `|∂u|²` is one-half the physical scalar energy.
 This is the squared-norm normalization for the real metric `2 Re h`. -/
theorem scalarGradientPair_eq_twice_gradNormSq {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) :
    scalarGradientPair h u u x = 2 * gradNormSq h u x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hf : DifferentiableAt ℝ (inChart x u) (chartPt x x) :=
    (contDiffAt_inChart hu x hz).differentiableAt (by simp)
  change chartGradientPair h x (inChart x u) (inChart x u) (chartPt x x) = _
  rw [chartGradientPair_eq_sum, realMetricFn_inverse h x hz]
  unfold gradNormSq dualNormMat
  rw [complex_dual_quadratic_realification]
  simp only [WithLp.ofLp_toLp]
  simp_rw [wirt_ofReal_real_coordinates hf]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, gMat]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- An actual metric differential operator-norm bound is exactly a bound
 on the physical scalar energy used by the integral estimates. -/
theorem scalarGradientPair_le_of_realDifferential_bound {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {K : ℝ} (hK : 0 ≤ K) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => L12Aux.underlyingRealTangentNormedAddCommGroup h y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => L12Aux.underlyingRealTangentInnerProductSpace h y
    ‖(NormedSpace.fromTangentSpace (u x)).toContinuousLinearMap ∘L
        mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) u x‖ ≤ K →
      scalarGradientPair h u u x ≤ K ^ 2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => L12Aux.underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => L12Aux.underlyingRealTangentInnerProductSpace h y
  intro hbound
  rw [scalarGradientPair_eq_realDifferential_opNorm_sq h hu x]
  exact pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) hbound 2

/-- A compact smooth cutoff with actual physical energy at most `K²`
 gives the localized energy bound required by Moser. The measure,
 integrability and zero extension outside the original ball are genuine. -/
theorem integral_scalar_cutoff_energy_bound {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u η : M.Carrier → ℝ}
    (hu : SmoothFn u) (hunonneg : ∀ y, 0 ≤ u y) (hsub : ∀ y, 0 ≤ laplacian g.form u y)
    (hη : SmoothFn η) (hcη : HasCompactSupport η) (x : M.Carrier)
    {r : ℝ} (hr : 0 < r) (hs : tsupport η ⊆ distBall g.form x r) (K : ℝ)
    (hηbound : ∀ y ∈ distBall g.form x r, scalarGradientPair g.form η η y ≤ K ^ 2) :
    (∫ y, scalarGradientPair g.form (fun z => η z * u z) (fun z => η z * u z) y ∂μ) ≤
      10 * K ^ 2 * ∫ y in distBall g.form x r, u y ^ 2 ∂μ := by
  have hR : Integrable (fun y => u y ^ 2 * scalarGradientPair g.form η η y) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hu 2) (smoothFn_scalarGradientPair g hη hη))
      (scalarGradientPair_hasCompactSupport g.form η η hcη).mul_left
  have hu2 := smoothFn_integrableOn_distBall g μ hμ (smoothFn_pow hu 2) x hr
  have hwhole : (∫ y in distBall g.form x r, u y ^ 2 * scalarGradientPair g.form η η y ∂μ) =
      ∫ y, u y ^ 2 * scalarGradientPair g.form η η y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [scalarGradientPair_zero_of_notMem_tsupport g.form η η (fun h => hy (hs h)), mul_zero]
  have hRbound := setIntegral_mono_on hR.integrableOn (hu2.const_mul (K ^ 2))
    (L12Aux.measurableSet_distBall g x r) (fun y hy => show
      u y ^ 2 * scalarGradientPair g.form η η y ≤ K ^ 2 * u y ^ 2 from
        (mul_le_mul_of_nonneg_left (hηbound y hy) (sq_nonneg (u y))).trans_eq (mul_comm _ _))
  rw [hwhole, integral_const_mul] at hRbound
  calc
    _ ≤ 10 * ∫ y, u y ^ 2 * scalarGradientPair g.form η η y ∂μ :=
      integral_scalar_cutoff_energy g hK μ hμ hu hunonneg hsub hη hcη
    _ ≤ 10 * (K ^ 2 * ∫ y in distBall g.form x r, u y ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hRbound (by norm_num)
    _ = _ := by ring

/-- The full local cutoff energy estimate for every positive real Moser
 power, with the right-hand side expressed as its original `2p` integral. -/
theorem integral_scalar_cutoff_energy_rpow_bound {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u η : M.Carrier → ℝ}
    (hu : SmoothFn u) (hpos : ∀ y, 0 < u y) (hsub : ∀ y, 0 ≤ laplacian g.form u y)
    {p : ℝ} (hp : 1 ≤ p) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) (hs : tsupport η ⊆ distBall g.form x r) (K : ℝ)
    (hηbound : ∀ y ∈ distBall g.form x r, scalarGradientPair g.form η η y ≤ K ^ 2) :
    (∫ y, scalarGradientPair g.form (fun z => η z * u z ^ p) (fun z => η z * u z ^ p) y ∂μ) ≤
      10 * K ^ 2 * ∫ y in distBall g.form x r, u y ^ (2 * p) ∂μ := by
  have hp2 (y : M.Carrier) : (u y ^ p) ^ 2 = u y ^ (2 * p) := by
    calc
      _ = u y ^ (p * 2) := (Real.rpow_mul_natCast (hpos y).le p 2).symm
      _ = _ := by rw [mul_comm p 2]
  have hE := integral_scalar_cutoff_energy_bound g hK μ hμ
    (smoothFn_rpow hu (fun y => ne_of_gt (hpos y)) p)
    (fun y => Real.rpow_nonneg (hpos y).le p) (laplacian_rpow_nonneg g.form hu hpos hsub hp)
    hη hcη x hr hs K hηbound
  simpa only [hp2] using hE

/-- Nonnegative subharmonic scalars, including their zeros, have the actual
 positive epsilon-regularized Moser energy estimate. No real power is
 differentiated through a zero. -/
theorem integral_scalar_cutoff_energy_regularized_rpow_bound {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u η : M.Carrier → ℝ}
    (hu : SmoothFn u) (hunonneg : ∀ y, 0 ≤ u y) (hsub : ∀ y, 0 ≤ laplacian g.form u y)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 1 ≤ p)
    (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) (hs : tsupport η ⊆ distBall g.form x r) (K : ℝ)
    (hηbound : ∀ y ∈ distBall g.form x r, scalarGradientPair g.form η η y ≤ K ^ 2) :
    (∫ y, scalarGradientPair g.form (fun z => η z * (u z + ε) ^ p)
      (fun z => η z * (u z + ε) ^ p) y ∂μ) ≤
      10 * K ^ 2 * ∫ y in distBall g.form x r, (u y + ε) ^ (2 * p) ∂μ := by
  have hv : SmoothFn (fun y => u y + ε) := fun a => (hu a).add contDiffOn_const
  have hvpos (y : M.Carrier) : 0 < u y + ε := add_pos_of_nonneg_of_pos (hunonneg y) hε
  have hvsub (y : M.Carrier) : 0 ≤ laplacian g.form (fun z => u z + ε) y := by
    rw [laplacian_add_const g.form hu ε y]
    exact hsub y
  exact integral_scalar_cutoff_energy_rpow_bound g hK μ hμ hv hvpos hvsub hp hη hcη x hr hs K hηbound

/-- Actual smooth scalars are bounded on every original finite-radius
 ball, using true properness rather than an assumed supremum field. -/
theorem smoothFn_boundedOn_distBall {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ distBall g.form x r, u y ≤ B := by
  obtain ⟨B, hB⟩ := (L12Aux.isCompact_inducedDistance_sublevel g x r).bddAbove_image
    (continuous_of_smoothFn hu).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun y hy => ?_⟩
  exact (hB ⟨y, ((L12Aux.mem_distBall_iff g x y hr).mp hy).le, rfl⟩).trans (le_max_left _ _)

/-- Uniform integral bounds along any real exponents tending to infinity
 give an everywhere bound for a continuous nonnegative scalar on an open
 set of finite full-support measure. This is the actual Moser limit step. -/
theorem continuous_le_of_rpow_integral_bounds {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {U : Set X} (hU : IsOpen U) (hUf : μ U < ⊤) {u : X → ℝ} (hu : Continuous u)
    (hunonneg : ∀ x ∈ U, 0 ≤ u x) {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hpTop : Tendsto p atTop atTop) {A B : ℝ} (hB : 0 < B)
    (hMom : ∀ j, IntegrableOn (fun x => u x ^ p j) U μ ∧
      (∫ x in U, u x ^ p j ∂μ) ≤ A * B ^ p j) :
    ∀ x ∈ U, u x ≤ B := by
  intro x hx
  by_contra hux
  have hux' : B < u x := lt_of_not_ge hux
  let c : ℝ := (B + u x) / 2
  have hBc : B < c := by dsimp [c]; linarith
  have hcu : c < u x := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := (lt_trans hB hBc).le
  let V : Set X := U ∩ {y | c < u y}
  have hV : IsOpen V := hU.inter (isOpen_lt continuous_const hu)
  have hVpos : 0 < μ V := hV.measure_pos μ ⟨x, hx, hcu⟩
  have hVfin : μ V < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUf
  have hmpos : 0 < μ.real V := ENNReal.toReal_pos hVpos.ne' hVfin.ne
  letI : IsFiniteMeasure (μ.restrict V) := ⟨by simpa only [Measure.restrict_apply_univ] using hVfin⟩
  have hlow (j : ℕ) : c ^ p j * μ.real V ≤ A * B ^ p j := by
    calc
      _ = ∫ y in V, c ^ p j ∂μ := by rw [setIntegral_const]; simp only [smul_eq_mul, mul_comm]
      _ ≤ ∫ y in V, u y ^ p j ∂μ :=
        setIntegral_mono_on (integrable_const _) ((hMom j).1.mono_set Set.inter_subset_left)
          hV.measurableSet (fun y hy => Real.rpow_le_rpow hc0 hy.2.le (hp0 j))
      _ ≤ ∫ y in U, u y ^ p j ∂μ :=
        setIntegral_mono_set (hMom j).1
          (ae_restrict_of_forall_mem hU.measurableSet (fun y hy => Real.rpow_nonneg (hunonneg y hy) _))
          (Filter.Eventually.of_forall fun y hy => hy.1)
      _ ≤ _ := (hMom j).2
  have hratio : 1 < c / B := (lt_div_iff₀ hB).mpr (by simpa only [one_mul] using hBc)
  have hdiv (j : ℕ) : (c / B) ^ p j ≤ A / μ.real V := by
    rw [Real.div_rpow hc0 hB.le, div_le_div_iff₀ (Real.rpow_pos_of_pos hB _) hmpos]
    exact hlow j
  have hlim := (tendsto_rpow_atTop_of_base_gt_one (c / B) hratio).comp hpTop
  obtain ⟨j, hj⟩ := (hlim.eventually (eventually_gt_atTop (A / μ.real V))).exists
  exact (not_lt_of_ge (hdiv j)) hj

/-- The actual Moser moment-limit step on every original positive-radius
 ball. Full support, finite volume and pointwise continuity are all
 obtained from the root's genuine metric and volume inside the proof. -/
theorem smoothFn_le_on_distBall_of_rpow_integral_bounds {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hunonneg : ∀ y, 0 ≤ u y)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hpTop : Tendsto p atTop atTop) {A B : ℝ} (hB : 0 < B)
    (hMom : ∀ j, IntegrableOn (fun y => u y ^ p j) (distBall g.form x r) μ ∧
      (∫ y in distBall g.form x r, u y ^ p j ∂μ) ≤ A * B ^ p j) :
    ∀ y ∈ distBall g.form x r, u y ≤ B := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  exact continuous_le_of_rpow_integral_bounds μ (L12Aux.isOpen_distBall g x r)
    (riemannianVolume_distBall_lt_top g μ hμ x hr) (continuous_of_smoothFn hu)
    (fun y _ => hunonneg y) hp0 hpTop hB hMom

/-- The summable exponential product in Moser iteration is uniformly
 bounded by an explicit constant depending only on its three numeric
 parameters. No geometric or analytic estimate is assumed here. -/
theorem geometric_exponential_iteration_bound {q A B : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (a : ℕ → ℝ) (ha0 : 0 ≤ a 0)
    (hrec : ∀ j, a (j + 1) ≤ Real.exp (q ^ j * (A + (j : ℝ) * B)) * a j) :
    ∀ j, a j ≤ Real.exp (A / (1 - q) + B * q / (1 - q) ^ 2) * a 0 := by
  let f : ℕ → ℝ := fun j => q ^ j * (A + (j : ℝ) * B)
  have hfpos (j : ℕ) : 0 ≤ f j :=
    mul_nonneg (pow_nonneg hq0 j) (add_nonneg hA (mul_nonneg (Nat.cast_nonneg j) hB))
  have hqn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hsum : HasSum f (A / (1 - q) + B * q / (1 - q) ^ 2) := by
    convert ((hasSum_geometric_of_lt_one hq0 hq1).mul_left A).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hqn).mul_left B) using 1
    · funext j
      dsimp [f]
      ring
    · simp only [div_eq_mul_inv]
      ring
  have hpartial (k : ℕ) : a k ≤ Real.exp (∑ j ∈ Finset.range k, f j) * a 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ Real.exp (f k) * a k := hrec k
        _ ≤ Real.exp (f k) * (Real.exp (∑ j ∈ Finset.range k, f j) * a 0) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = _ := by rw [Finset.sum_range_succ, Real.exp_add]; ring
  intro j
  have hsumle : (∑ k ∈ Finset.range j, f k) ≤ A / (1 - q) + B * q / (1 - q) ^ 2 :=
    sum_le_hasSum (Finset.range j) (fun k _ => hfpos k) hsum
  exact (hpartial j).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsumle) ha0)

/-- The zero-integral branch of the original mean estimate is pointwise
 zero on the actual ball, by genuine continuity and full-support volume. -/
theorem smoothFn_eq_zero_on_distBall_of_integral_eq_zero {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hunonneg : ∀ y, 0 ≤ u y)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r)
    (hzero : (∫ y in distBall g.form x r, u y ∂μ) = 0) :
    ∀ y ∈ distBall g.form x r, u y = 0 := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hI := smoothFn_integrableOn_distBall g μ hμ hu x hr
  have hae : u =ᵐ[μ.restrict (distBall g.form x r)] (fun _ => 0) :=
    (integral_eq_zero_iff_of_nonneg (fun y => hunonneg y) hI).mp hzero
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae (L12Aux.isOpen_distBall g x r)
    (continuous_of_smoothFn hu).continuousOn continuousOn_const

open Set

/-- The displacement bound from genuine calculus remains valid with a
 finite exceptional derivative set. The finite subdivision and endpoint
 continuity are handled internally, as needed for project piecewise C¹ curves. -/
theorem norm_sub_le_integral_of_deriv_bound_off_finset {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ℝ) {f : ℝ → E} {B : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ioo a b, t ∉ s → DifferentiableAt ℝ f t)
    (hfB : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ B t)
    (hBi : IntervalIntegrable B volume a b) :
    ‖f b - f a‖ ≤ ∫ t in a..b, B t := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
    apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc
      (fun t ht => (hfd t ht (by simp)).differentiableWithinAt) hfB hBi
  | @insert c s hcs ih =>
    by_cases hc : c ∈ Ioo a b
    · have hBiL : IntervalIntegrable B volume a c := hBi.mono_set (by
        rw [uIcc_of_le hc.1.le, uIcc_of_le hab]
        intro t ht
        exact ⟨ht.1, ht.2.trans hc.2.le⟩)
      have hBiR : IntervalIntegrable B volume c b := hBi.mono_set (by
        rw [uIcc_of_le hc.2.le, uIcc_of_le hab]
        intro t ht
        exact ⟨hc.1.le.trans ht.1, ht.2⟩)
      have hL : ‖f c - f a‖ ≤ ∫ t in a..c, B t := by
        apply ih hc.1.le (hfc.mono (fun t ht => ⟨ht.1, ht.2.trans hc.2.le⟩))
        · intro t ht hts
          exact hfd t ⟨ht.1, ht.2.trans hc.2⟩ (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt ht.2, hts⟩)
        · exact hfB.mono (fun t h ht => h ⟨ht.1, ht.2.trans hc.2⟩)
        · exact hBiL
      have hR : ‖f b - f c‖ ≤ ∫ t in c..b, B t := by
        apply ih hc.2.le (hfc.mono (fun t ht => ⟨hc.1.le.trans ht.1, ht.2⟩))
        · intro t ht hts
          exact hfd t ⟨hc.1.trans ht.1, ht.2⟩ (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt ht.1, hts⟩)
        · exact hfB.mono (fun t h ht => h ⟨hc.1.trans ht.1, ht.2⟩)
        · exact hBiR
      calc
        _ ≤ ‖f b - f c‖ + ‖f c - f a‖ := by
          simpa only [dist_eq_norm] using dist_triangle (f b) (f c) (f a)
        _ ≤ (∫ t in c..b, B t) + ∫ t in a..c, B t := add_le_add hR hL
        _ = _ := by rw [add_comm]; exact intervalIntegral.integral_add_adjacent_intervals hBiL hBiR
    · apply ih hab hfc
      · intro t ht hts
        have htc : t ≠ c := by intro he; exact hc (he ▸ ht)
        exact hfd t ht (by simp only [Finset.mem_insert, not_or]; exact ⟨htc, hts⟩)
      · exact hfB
      · exact hBi

/-- The project's actual piecewise C¹ curve is differentiable as a real
 manifold map at every interior non-breakpoint. -/
theorem piecewiseCurve_mdifferentiableAt_real {n : ℕ} {M : ComplexManifold n}
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) {t : ℝ}
    (ht : t ∈ Ioo 0 1) (hb : t ∉ γ.breakpoints) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ t := by
  letI := L12Aux.manifold_realSmooth M
  have hcont : ContinuousAt γ.toFun t := γ.continuous_on.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hdiff := (γ.piecewise_c1 t hb).differentiableAt (by norm_num)
  rw [mdifferentiableAt_iff]
  refine ⟨hcont, ?_⟩
  convert! hdiff.differentiableWithinAt using 1 <;>
    simp [writtenInExtChartAt, L12Aux.real_extChartAt_eq, mfld_simps]

/-- Actual scalar differentiation along the project's piecewise curve,
 expressed through the genuine real manifold differential and velocity. -/
theorem scalar_curve_hasDerivAt {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) {t : ℝ} (ht : t ∈ Ioo 0 1) (hb : t ∉ γ.breakpoints) :
    HasDerivAt (fun s => u (γ s))
      (mvfderiv 𝓘(ℝ, ComplexVector n) u (γ t) (L12Aux.realCurveVelocity γ t)) t := by
  letI := L12Aux.manifold_realSmooth M
  have hγ := piecewiseCurve_mdifferentiableAt_real γ ht hb
  have huM := (contMDiff_real_of_smoothFn hu (γ t)).mdifferentiableAt (by simp)
  have hcomp : DifferentiableAt ℝ (fun s => u (γ s)) t := by
    exact mdifferentiableAt_iff_differentiableAt.mp (huM.comp t hγ)
  have hchain := mvfderiv_comp_apply t huM hγ
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)
  rw [mvfderiv_eq_fderiv] at hchain
  change deriv (fun s => u (γ s)) t =
    mvfderiv 𝓘(ℝ, ComplexVector n) u (γ t) (L12Aux.realCurveVelocity γ t) at hchain
  rw [← hchain]
  exact hcomp.hasDerivAt

/-- The derivative along a genuine piecewise curve is controlled by the
 physical scalar gradient times the curve's original metric speed. -/
theorem scalar_curve_norm_deriv_le {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u) {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) {t : ℝ} (ht : t ∈ Ioo 0 1) (hb : t ∉ γ.breakpoints) :
    ‖deriv (fun s => u (γ s)) t‖ ≤
      Real.sqrt (scalarGradientPair h u u (γ t)) * curveSpeed h γ t := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup h z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentInnerProductSpace h z
  have hnorm : ‖mvfderiv 𝓘(ℝ, ComplexVector n) u (γ t)‖ =
      Real.sqrt (scalarGradientPair h u u (γ t)) := by
    rw [scalarGradientPair_eq_realDifferential_opNorm_sq h hu (γ t)]
    exact (Real.sqrt_sq (ContinuousLinearMap.opNorm_nonneg _)).symm
  rw [(scalar_curve_hasDerivAt hu γ ht hb).deriv]
  calc
    _ ≤ ‖mvfderiv 𝓘(ℝ, ComplexVector n) u (γ t)‖ * ‖L12Aux.realCurveVelocity γ t‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hnorm, L12Aux.realCurveVelocity_norm h γ ht hb]

/-- The full scalar fundamental theorem estimate on every admitted curve.
 Integrability of the variable gradient-speed product follows internally
 from genuine metric smoothness, compact parameter interval and the curve's
 required integrable speed; finite breakpoints contribute no boundary term. -/
theorem scalar_curve_FTC {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {u : M.Carrier → ℝ} (hu : SmoothFn u) {x y : M.Carrier}
    (γ : IntegrableCurve g.form x y) :
    |u y - u x| ≤ ∫ t in Icc (0 : ℝ) 1,
      Real.sqrt (scalarGradientPair g.form u u (γ.1 t)) * curveSpeed g.form γ.1 t := by
  have hgrad : ContinuousOn (fun t => Real.sqrt (scalarGradientPair g.form u u (γ.1 t))) (Icc 0 1) :=
    (Real.continuous_sqrt.comp (continuous_of_smoothFn (smoothFn_scalarGradientPair g hu hu))).comp_continuousOn
      γ.1.continuous_on
  have hBint : IntegrableOn (fun t => Real.sqrt (scalarGradientPair g.form u u (γ.1 t)) *
      curveSpeed g.form γ.1 t) (Icc 0 1) := IntegrableOn.continuousOn_mul hgrad γ.2 isCompact_Icc
  have hBi := (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := (volume : Measure ℝ)) zero_le_one).mpr hBint
  have hfc : ContinuousOn (fun t => u (γ.1 t)) (Icc 0 1) :=
    (continuous_of_smoothFn hu).comp_continuousOn γ.1.continuous_on
  have hbAE : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ γ.1.breakpoints :=
    γ.1.breakpoints.finite_toSet.countable.ae_notMem volume
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo 0 1 →
      ‖deriv (fun s => u (γ.1 s)) t‖ ≤
        Real.sqrt (scalarGradientPair g.form u u (γ.1 t)) * curveSpeed g.form γ.1 t := by
    filter_upwards [hbAE] with t hb
    intro ht
    exact scalar_curve_norm_deriv_le g.form hu γ.1 ht hb
  have hp := norm_sub_le_integral_of_deriv_bound_off_finset γ.1.breakpoints zero_le_one hfc
    (fun t ht hb => (scalar_curve_hasDerivAt hu γ.1 ht hb).differentiableAt) hbound hBi
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at hp
  change |u (γ.1 1) - u (γ.1 0)| ≤ _ at hp
  simpa only [γ.1.finish_eq, γ.1.start_eq] using hp

/-- Mean oscillation is bounded by the genuine pairwise oscillation
 integral. All finite-measure product integrability is proved internally. -/
theorem integral_abs_sub_average_le_pairwise {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ0 : μ univ ≠ 0)
    {f : X → ℝ} (hf : Integrable f μ) :
    (∫ x, |f x - (μ.real univ)⁻¹ * ∫ y, f y ∂μ| ∂μ) ≤
      (μ.real univ)⁻¹ * ∫ x, ∫ y, |f x - f y| ∂μ ∂μ := by
  let m := μ.real univ
  have hmpos : 0 < m := ENNReal.toReal_pos hμ0 (measure_ne_top μ univ)
  have hPair : Integrable (fun p : X × X => |f p.1 - f p.2|) (μ.prod μ) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hf.comp_fst μ).sub (hf.comp_snd μ)).norm
  have hInner := hPair.integral_prod_left
  have hdev : Integrable (fun x => |f x - m⁻¹ * ∫ y, f y ∂μ|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub (integrable_const _)).norm
  have hpoint (x : X) : |f x - m⁻¹ * ∫ y, f y ∂μ| ≤
      m⁻¹ * ∫ y, |f x - f y| ∂μ := by
    have heq : f x - m⁻¹ * (∫ y, f y ∂μ) = m⁻¹ * ∫ y, (f x - f y) ∂μ := by
      rw [integral_sub (integrable_const _) hf, integral_const]
      change f x - m⁻¹ * (∫ y, f y ∂μ) = m⁻¹ * (m * f x - ∫ y, f y ∂μ)
      field_simp [ne_of_gt hmpos]
    rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hmpos.le)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hmpos.le)
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => f x - f y)
  have hp := integral_mono hdev (hInner.const_mul m⁻¹) hpoint
  rw [integral_const_mul] at hp
  exact hp

/-- The actual original-ball mean oscillation is controlled by its
 pairwise integral, with finite positive volume and scalar integrability
 derived from the genuine root geometry. -/
theorem integral_distBall_abs_sub_average_le_pairwise {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) {r : ℝ} (hr : 0 < r) :
    (∫ y in distBall g.form x r,
      |u y - (μ.real (distBall g.form x r))⁻¹ * ∫ z in distBall g.form x r, u z ∂μ| ∂μ) ≤
      (μ.real (distBall g.form x r))⁻¹ *
        ∫ y in distBall g.form x r, ∫ z in distBall g.form x r, |u y - u z| ∂μ ∂μ := by
  letI : IsFiniteMeasure (μ.restrict (distBall g.form x r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using riemannianVolume_distBall_lt_top g μ hμ x hr⟩
  have hpos : (μ.restrict (distBall g.form x r)) univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact (riemannianVolume_distBall_pos g μ hμ x hr).ne'
  have hp := integral_abs_sub_average_le_pairwise (μ.restrict (distBall g.form x r)) hpos
    (smoothFn_integrableOn_distBall g μ hμ hu x hr)
  simpa only [Measure.real, Measure.restrict_apply_univ] using hp

/-- Normalized positive moments bounded uniformly on shrinking original
 balls control the center value. This version needs no exponent-limit
 assumption and therefore also handles the fixed-ratio cutoff iteration. -/
theorem smoothFn_center_le_of_shrinking_ball_moments {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hpos : ∀ y, 0 < u y) (x : M.Carrier)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (hrTop : Tendsto r atTop (𝓝 0))
    {p : ℕ → ℝ} (hp : ∀ j, 0 < p j) {B : ℝ} (hB : 0 < B)
    (hMom : ∀ j, (∫ y in distBall g.form x (r j), u y ^ p j ∂μ) ≤
      B ^ p j * μ.real (distBall g.form x (r j))) :
    u x ≤ B := by
  classical
  letI := L12Aux.inducedMetricSpace g
  by_contra hux
  have hux' : B < u x := lt_of_not_ge hux
  let c := (B + u x) / 2
  have hBc : B < c := by dsimp [c]; linarith
  have hcu : c < u x := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := (hB.trans hBc).le
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const (continuous_of_smoothFn hu)).mem_nhds hcu)
  obtain ⟨j, hj⟩ := (hrTop.eventually (Iio_mem_nhds hδ)).exists
  let S := distBall g.form x (r j)
  have hS : MeasurableSet S := L12Aux.measurableSet_distBall g x (r j)
  have hSf : μ S < ⊤ := riemannianVolume_distBall_lt_top g μ hμ x (hr j)
  have hSpos : 0 < μ.real S :=
    ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ x (hr j)).ne' hSf.ne
  letI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hSf⟩
  have hinside (y : M.Carrier) (hy : y ∈ S) : c < u y := by
    have hym : y ∈ @Metric.ball M.Carrier (L12Aux.inducedMetricSpace g).toPseudoMetricSpace x (r j) := by
      rw [← L12Aux.distBall_eq_metric_ball g x (hr j)]
      exact hy
    exact hδsub (Metric.ball_subset_ball hj.le hym)
  have hI := smoothFn_integrableOn_distBall g μ hμ
    (smoothFn_rpow hu (fun y => (hpos y).ne') (p j)) x (hr j)
  have hweighted : c ^ p j * μ.real S ≤ B ^ p j * μ.real S := by
    calc
      _ = ∫ y in S, c ^ p j ∂μ := by rw [setIntegral_const]; simp only [smul_eq_mul, mul_comm]
      _ ≤ ∫ y in S, u y ^ p j ∂μ := setIntegral_mono_on (integrable_const _) hI hS
        (fun y hy => Real.rpow_le_rpow hc0 (hinside y hy).le (hp j).le)
      _ ≤ _ := hMom j
  have hstrict := mul_lt_mul_of_pos_right (Real.rpow_lt_rpow hB.le hBc (hp j)) hSpos
  exact (not_le_of_gt hstrict) hweighted

open Metric

/-- The local weak maximal estimate from a genuine five-ball covering.
 The witness radii and their measured enlargement bound are explicit;
 countability, disjoint integral summation and the full estimate are proved. -/
theorem weak_ball_family_measure_bound {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (t : Set X) (r : X → ℝ) (R : ℝ)
    (hrpos : ∀ x ∈ t, 0 < r x) (hrupper : ∀ x ∈ t, r x ≤ R)
    (g : X → ℝ≥0∞) (tLevel D : ℝ≥0∞)
    (hgrowth : ∀ x ∈ t, μ (ball x (5 * r x)) ≤ D * μ (ball x (r x)))
    (hwitness : ∀ x ∈ t, tLevel * μ (ball x (r x)) ≤ ∫⁻ y in ball x (r x), g y ∂μ) :
    tLevel * μ t ≤ D * ∫⁻ y, g y ∂μ := by
  classical
  obtain ⟨v, hvt, hvdisj, hvcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball t id r R hrupper 5 (by norm_num)
  have hvcount : v.Countable := hvdisj.countable_of_isOpen
    (fun x _ => isOpen_ball) (fun x hx => ⟨x, mem_ball_self (hrpos x (hvt hx))⟩)
  letI : Countable v := hvcount.to_subtype
  have hcover : t ⊆ ⋃ i : v, ball (i : X) (5 * r i) := by
    intro x hx
    obtain ⟨y, hy, hsub⟩ := hvcover x hx
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hsub (mem_ball_self (hrpos x hx))⟩
  have hdisj : Pairwise (fun i j : v => Disjoint (ball (i : X) (r i)) (ball (j : X) (r j))) := by
    intro i j hij
    exact hvdisj i.property j.property (fun h => hij (Subtype.ext h))
  have hterm (i : v) : tLevel * μ (ball (i : X) (5 * r i)) ≤
      D * ∫⁻ y in ball (i : X) (r i), g y ∂μ := by
    calc
      _ ≤ tLevel * (D * μ (ball (i : X) (r i))) := by
        simpa only [mul_comm] using mul_le_mul_left (hgrowth i (hvt i.property)) tLevel
      _ = D * (tLevel * μ (ball (i : X) (r i))) := by ac_rfl
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_left (hwitness i (hvt i.property)) D
  calc
    _ ≤ tLevel * μ (⋃ i : v, ball (i : X) (5 * r i)) := by
      simpa only [mul_comm] using mul_le_mul_left (measure_mono hcover) tLevel
    _ ≤ tLevel * ∑' i : v, μ (ball (i : X) (5 * r i)) := by
      simpa only [mul_comm] using mul_le_mul_left
        (measure_iUnion_le (μ := μ) (fun i : v => ball (i : X) (5 * r i))) tLevel
    _ = ∑' i : v, tLevel * μ (ball (i : X) (5 * r i)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' i : v, D * ∫⁻ y in ball (i : X) (r i), g y ∂μ := ENNReal.tsum_le_tsum hterm
    _ = D * ∑' i : v, ∫⁻ y in ball (i : X) (r i), g y ∂μ := ENNReal.tsum_mul_left
    _ = D * ∫⁻ y in ⋃ i : v, ball (i : X) (r i), g y ∂μ := by
      rw [lintegral_iUnion (fun _ => isOpen_ball.measurableSet) hdisj]
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_left
        (lintegral_mono' (μ := μ.restrict (⋃ i : v, ball (i : X) (r i))) Measure.restrict_le_self (le_refl g)) D

/-- The genuine first scalar composition rule in any real chart direction. -/
theorem rDeriv_scalar_comp {n : ℕ} {f : ComplexVector n → ℝ} {F : ℝ → ℝ}
    {z : ComplexVector n} (hf : DifferentiableAt ℝ f z) (hF : DifferentiableAt ℝ F (f z))
    (a : RIdx n) :
    rDeriv (F ∘ f) z a = deriv F (f z) * rDeriv f z a := by
  unfold rDeriv
  rw [fderiv_comp z hF hf]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]

/-- Actual chart metric energy obeys the first-variable scalar chain rule. -/
theorem chartGradientPair_scalar_comp_left {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {f : ComplexVector n → ℝ} (k : ComplexVector n → ℝ)
    {F : ℝ → ℝ} {z : ComplexVector n} (hf : DifferentiableAt ℝ f z)
    (hF : DifferentiableAt ℝ F (f z)) :
    chartGradientPair h x (F ∘ f) k z = deriv F (f z) * chartGradientPair h x f k z := by
  rw [chartGradientPair_eq_sum, chartGradientPair_eq_sum]
  simp_rw [rDeriv_scalar_comp hf hF]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The intrinsic physical energy has the actual scalar chain rule, without
 requiring the other scalar to have any extra regularity. -/
theorem scalarGradientPair_scalar_comp_left {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (v : M.Carrier → ℝ) (F : ℝ → ℝ) (x : M.Carrier) (hF : DifferentiableAt ℝ F (u x)) :
    scalarGradientPair h (fun y => F (u y)) v x = deriv F (u x) * scalarGradientPair h u v x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hf : DifferentiableAt ℝ (inChart x u) (chartPt x x) :=
    (contDiffAt_inChart hu x hz).differentiableAt (by simp)
  have hval : inChart x u (chartPt x x) = u x :=
    congrArg u ((extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x))
  have hF' : DifferentiableAt ℝ F (inChart x u (chartPt x x)) := by rw [hval]; exact hF
  have hp := chartGradientPair_scalar_comp_left h x (inChart x v) hf hF'
  rw [hval] at hp
  exact hp

/-- Actual physical energy of a scalar composition, including the square
 of the genuine first derivative. This supplies smooth level truncations. -/
theorem scalarGradientPair_scalar_comp_self {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (F : ℝ → ℝ) (x : M.Carrier) (hF : DifferentiableAt ℝ F (u x)) :
    scalarGradientPair h (fun y => F (u y)) (fun y => F (u y)) x =
      deriv F (u x) ^ 2 * scalarGradientPair h u u x := by
  rw [scalarGradientPair_scalar_comp_left h hu (fun y => F (u y)) F x hF,
    scalarGradientPair_symm h u (fun y => F (u y)) x,
    scalarGradientPair_scalar_comp_left h hu u F x hF]
  ring

/-- The real-power energy formula is the true chain rule for the original
 metric, valid at every nonzero scalar even for nonintegral exponents. -/
theorem scalarGradientPair_rpow_self {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (p : ℝ) (x : M.Carrier) (hne : u x ≠ 0) :
    scalarGradientPair h (fun y => u y ^ p) (fun y => u y ^ p) x =
      (p * u x ^ (p - 1)) ^ 2 * scalarGradientPair h u u x := by
  rw [scalarGradientPair_scalar_comp_self h hu (fun t : ℝ => t ^ p) x
    (Real.hasDerivAt_rpow_const (Or.inl hne)).differentiableAt, Real.deriv_rpow_const]

/-- Global smooth real scalar composition preserves the project's exact
 all-chart smoothness predicate. -/
theorem smoothFn_scalar_comp {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) :
    SmoothFn (fun y => F (u y)) := fun x => hF.comp_contDiffOn (hu x)

/-- The actual weak estimate for the set where some bounded-radius ball
 average exceeds a level. Witness choice is internal and no measurability
 of an uncountable supremum is assumed. -/
theorem weak_local_average_superlevel_measure {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (R : ℝ) (g : X → ℝ≥0∞) (tLevel D : ℝ≥0∞)
    (hgrowth : ∀ (x : X) (ρ : ℝ), 0 < ρ → ρ ≤ R →
      μ (ball x (5 * ρ)) ≤ D * μ (ball x ρ)) :
    tLevel * μ {x | ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      tLevel * μ (ball x ρ) < ∫⁻ y in ball x ρ, g y ∂μ} ≤ D * ∫⁻ y, g y ∂μ := by
  classical
  let E : Set X := {x | ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
    tLevel * μ (ball x ρ) < ∫⁻ y in ball x ρ, g y ∂μ}
  let r : X → ℝ := fun x => if hx : x ∈ E then Classical.choose hx else 0
  have hspec (x : X) (hx : x ∈ E) : 0 < r x ∧ r x ≤ R ∧
      tLevel * μ (ball x (r x)) < ∫⁻ y in ball x (r x), g y ∂μ := by
    dsimp only [r]
    rw [dif_pos hx]
    exact Classical.choose_spec hx
  exact weak_ball_family_measure_bound μ E r R
    (fun x hx => (hspec x hx).1) (fun x hx => (hspec x hx).2.1) g tLevel D
    (fun x hx => hgrowth x (r x) (hspec x hx).1 (hspec x hx).2.1)
    (fun x hx => (hspec x hx).2.2.le)

/-- Averaging deviation from any constant is controlled by averaging its
 absolute deviation, with finite-volume normalization proved internally. -/
theorem abs_average_sub_le_average_abs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ0 : μ univ ≠ 0)
    {f : X → ℝ} (hf : Integrable f μ) (c : ℝ) :
    |(μ.real univ)⁻¹ * (∫ y, f y ∂μ) - c| ≤
      (μ.real univ)⁻¹ * ∫ y, |f y - c| ∂μ := by
  let m := μ.real univ
  have hmpos : 0 < m := ENNReal.toReal_pos hμ0 (measure_ne_top μ univ)
  have heq : m⁻¹ * (∫ y, f y ∂μ) - c = m⁻¹ * ∫ y, (f y - c) ∂μ := by
    rw [integral_sub hf (integrable_const _), integral_const]
    change m⁻¹ * (∫ y, f y ∂μ) - c = m⁻¹ * ((∫ y, f y ∂μ) - m * c)
    field_simp [ne_of_gt hmpos] <;> ring
  rw [show (μ.real univ)⁻¹ * (∫ y, f y ∂μ) - c =
    m⁻¹ * ∫ y, (f y - c) ∂μ from heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hmpos.le)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => f y - c))
    (inv_nonneg.mpr hmpos.le)

/-- The actual original-ball average has the genuine absolute-deviation
 estimate, with its positive finite volume and integrability derived. -/
theorem abs_distBall_average_sub_le {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) {r : ℝ} (hr : 0 < r) (c : ℝ) :
    |(μ.real (distBall g.form x r))⁻¹ * (∫ y in distBall g.form x r, u y ∂μ) - c| ≤
      (μ.real (distBall g.form x r))⁻¹ * ∫ y in distBall g.form x r, |u y - c| ∂μ := by
  letI : IsFiniteMeasure (μ.restrict (distBall g.form x r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using riemannianVolume_distBall_lt_top g μ hμ x hr⟩
  have hpos : (μ.restrict (distBall g.form x r)) univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact (riemannianVolume_distBall_pos g μ hμ x hr).ne'
  have hp := abs_average_sub_le_average_abs (μ.restrict (distBall g.form x r)) hpos
    (smoothFn_integrableOn_distBall g μ hμ hu x hr) c
  simpa only [Measure.real, Measure.restrict_apply_univ] using hp

/-- Smooth scalar averages on shrinking original distance balls converge
 at every center to the scalar itself. No differentiation theorem, Ricci
 estimate or doubling assumption enters this continuity argument. -/
theorem distBall_average_tendsto {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (hrTop : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => (μ.real (distBall g.form x (r j)))⁻¹ *
      ∫ y in distBall g.form x (r j), u y ∂μ) atTop (𝓝 (u x)) := by
  letI := L12Aux.inducedMetricSpace g
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hU : IsOpen {y | |u y - u x| < ε / 2} :=
    isOpen_lt ((continuous_of_smoothFn hu).sub continuous_const).abs continuous_const
  have hxU : x ∈ {y | |u y - u x| < ε / 2} := by simpa only [mem_setOf_eq, sub_self, abs_zero] using hhalf
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  filter_upwards [hrTop.eventually (Iio_mem_nhds hδ)] with j hj
  have hSf := riemannianVolume_distBall_lt_top g μ hμ x (hr j)
  have hmpos : 0 < μ.real (distBall g.form x (r j)) :=
    ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ x (hr j)).ne' hSf.ne
  letI : IsFiniteMeasure (μ.restrict (distBall g.form x (r j))) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hSf⟩
  have hIabs : IntegrableOn (fun y => |u y - u x|) (distBall g.form x (r j)) μ := by
    change Integrable (fun y => |u y - u x|) (μ.restrict (distBall g.form x (r j)))
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((smoothFn_integrableOn_distBall g μ hμ hu x (hr j)).sub (integrable_const (u x))).norm
  have hbound : (∫ y in distBall g.form x (r j), |u y - u x| ∂μ) ≤
      μ.real (distBall g.form x (r j)) * (ε / 2) := by
    have hp := setIntegral_mono_on hIabs (integrable_const (ε / 2))
      (L12Aux.measurableSet_distBall g x (r j)) (fun y hy => show |u y - u x| ≤ ε / 2 from
        (hδsub (Metric.ball_subset_ball hj.le (by
          rw [← L12Aux.distBall_eq_metric_ball g x (hr j)]
          exact hy))).le)
    simpa only [setIntegral_const, smul_eq_mul] using hp
  have hdev := abs_distBall_average_sub_le g μ hμ hu x (hr j) (u x)
  have hsmall : |(μ.real (distBall g.form x (r j)))⁻¹ *
      (∫ y in distBall g.form x (r j), u y ∂μ) - u x| ≤ ε / 2 := by
    calc
      _ ≤ _ := hdev
      _ ≤ (μ.real (distBall g.form x (r j)))⁻¹ *
          (μ.real (distBall g.form x (r j)) * (ε / 2)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hmpos.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmpos), one_mul]
  simpa only [Real.dist_eq] using hsmall.trans_lt (half_lt_self hε)

/-- Actual chart transport of integrability uses only the original AE
 integrable representative. It holds for arbitrary real normed targets;
 no pointwise measurability of the input function is imposed. -/
theorem integrableOn_chart_volume_smul {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M.Carrier → F} (hf : IntegrableOn f (extChartAt (ComplexModel n) a).source μ) :
    IntegrableOn (fun z => Real.sqrt (realMetricFn g.form a z).det • f (chartInv a z))
      (chartTarget a) (lebesgueC n) := by
  let ν := (lebesgueC n).restrict (chartTarget a)
  let d : ComplexVector n → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det)
  have ht : MeasurableSet (chartTarget a) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable d ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((volumeDensity_continuousOn g a).aemeasurable ht)
  have hmap : Integrable f (Measure.map (chartInvExtension a) (ν.withDensity d)) := by
    rw [← riemannianVolume_restrict_eq_map g.form μ hμ a]
    exact hf
  have hcomp : Integrable (f ∘ chartInvExtension a) (ν.withDensity d) :=
    hmap.comp_measurable (chartInvExtension_measurable a)
  have hw := (integrable_withDensity_iff_integrable_smul₀' hd
    (ae_of_all ν (fun _ => ENNReal.ofReal_lt_top))).mp hcomp
  change Integrable (fun z => Real.sqrt (realMetricFn g.form a z).det • f (chartInv a z)) ν
  apply hw.congr
  filter_upwards [ae_restrict_mem ht] with z hz
  simp only [d, Function.comp_apply, chartInvExtension, if_pos hz,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- AE strong measurability in the original volume pulls to unweighted
 chart Lebesgue measure. The density is cancelled using its actual strict
 positivity on the chart target, not an added measurability premise on `f`. -/
theorem aestronglyMeasurable_chartInv_of_volume {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier) {F : Type*} [NormedAddCommGroup F] {f : M.Carrier → F}
    (hf : AEStronglyMeasurable f (μ.restrict (extChartAt (ComplexModel n) a).source)) :
    AEStronglyMeasurable (fun z => f (chartInv a z)) ((lebesgueC n).restrict (chartTarget a)) := by
  let ν := (lebesgueC n).restrict (chartTarget a)
  let d : ComplexVector n → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det)
  have ht : MeasurableSet (chartTarget a) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable d ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((volumeDensity_continuousOn g a).aemeasurable ht)
  have hnz : ∀ᵐ z ∂ν, d z ≠ 0 :=
    ae_restrict_of_forall_mem ht (fun z hz => ne_of_gt (ENNReal.ofReal_pos.mpr
      (L12Aux.volumeDensity_pos g.form a z hz)))
  have hac : ν ≪ ν.withDensity d := withDensity_absolutelyContinuous' hd hnz
  have hmap : AEStronglyMeasurable f (Measure.map (chartInvExtension a) (ν.withDensity d)) := by
    rw [← riemannianVolume_restrict_eq_map g.form μ hμ a]
    exact hf
  have hcomp : AEStronglyMeasurable (f ∘ chartInvExtension a) (ν.withDensity d) :=
    hmap.comp_measurable (chartInvExtension_measurable a)
  apply (AEStronglyMeasurable.mono_ac hac hcomp).congr
  filter_upwards [ae_restrict_mem ht] with z hz
  simp only [Function.comp_apply, chartInvExtension, if_pos hz]

/-- Full chart integral transport in a real normed target for an AE strongly
 measurable original-volume representative, with no extra pointwise
 measurability or integrability assumption. -/
theorem integral_chart_volume_ae {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M.Carrier → F}
    (hf : AEStronglyMeasurable f (μ.restrict (extChartAt (ComplexModel n) a).source)) :
    (∫ y in (extChartAt (ComplexModel n) a).source, f y ∂μ) =
      ∫ z in chartTarget a, Real.sqrt (realMetricFn g.form a z).det • f (chartInv a z) ∂lebesgueC n := by
  let ν := (lebesgueC n).restrict (chartTarget a)
  let d : ComplexVector n → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det)
  have ht : MeasurableSet (chartTarget a) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable d ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((volumeDensity_continuousOn g a).aemeasurable ht)
  have hmap : AEStronglyMeasurable f (Measure.map (chartInvExtension a) (ν.withDensity d)) := by
    rw [← riemannianVolume_restrict_eq_map g.form μ hμ a]
    exact hf
  change (∫ y, f y ∂μ.restrict (extChartAt (ComplexModel n) a).source) =
    ∫ z, Real.sqrt (realMetricFn g.form a z).det • f (chartInv a z) ∂ν
  rw [riemannianVolume_restrict_eq_map g.form μ hμ a,
    integral_map (chartInvExtension_measurable a).aemeasurable hmap,
    integral_withDensity_eq_integral_toReal_smul₀ hd (ae_of_all ν (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem ht] with z hz
  simp only [d, chartInvExtension, if_pos hz, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- Uniform actual scalar energy cutoffs. The numerical constant is chosen
 before the manifold, metric, center and radius; every original positive
 radius is covered. The support lies strictly in the original triple ball. -/
theorem exists_uniform_scalar_energy_cutoffs (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (x : M.Carrier) (R : ℝ), 0 < R →
      ∃ η : M.Carrier → ℝ,
        ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
        (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form x y ≤ R → η y = 1) ∧
        tsupport η ⊆ distBall g.form x (3 * R) ∧
        ∀ y, scalarGradientPair g.form η η y ≤ (C / R) ^ 2 := by
  obtain ⟨C, hC, hCut⟩ := L12Aux.exists_quantitative_smooth_distance_cutoffs n
  refine ⟨C, hC, ?_⟩
  intro M g x R hR
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentInnerProductSpace g.form z
  obtain ⟨η, hηC, hη, hcη, hηrange, hηone, hηsupport, hηderiv⟩ := hCut M g x R hR
  refine ⟨η, hηC, hη, hcη, hηrange, hηone, ?_, ?_⟩
  · intro y hy
    have hd : inducedDistance g.form x y ≤ 2 * R := hηsupport hy
    apply (L12Aux.mem_distBall_iff g x y (show 0 < 3 * R by positivity)).mpr
    linarith
  · intro y
    apply scalarGradientPair_le_of_realDifferential_bound g.form hη y (div_nonneg hC.le hR.le)
    change ‖L12Aux.realDifferential g η y‖ ≤ C / R
    exact hηderiv y

/-- The uniform regularized Moser energy estimate, now with an actual
 constructed smooth compact cutoff rather than an extra cutoff premise.
 Its dimensional constant precedes all geometric and analytic input data. -/
theorem exists_uniform_scalar_moser_energy_cutoffs (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsKahler g →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (u : M.Carrier → ℝ), SmoothFn u → (∀ y, 0 ≤ u y) →
        (∀ y, 0 ≤ laplacian g.form u y) → ∀ (x : M.Carrier) (R : ℝ), 0 < R →
        ∀ (ε p : ℝ), 0 < ε → 1 ≤ p →
        ∃ η : M.Carrier → ℝ,
          ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
          (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧
          (∀ y, inducedDistance g.form x y ≤ R → η y = 1) ∧
          tsupport η ⊆ distBall g.form x (3 * R) ∧
          (∫ y, scalarGradientPair g.form (fun z => η z * (u z + ε) ^ p)
            (fun z => η z * (u z + ε) ^ p) y ∂μ) ≤
              C / R ^ 2 * ∫ y in distBall g.form x (3 * R), (u y + ε) ^ (2 * p) ∂μ := by
  obtain ⟨A, hA, hCuts⟩ := exists_uniform_scalar_energy_cutoffs n
  refine ⟨10 * A ^ 2, by positivity, ?_⟩
  intro M g hK μ hμ u hu hunonneg hsub x R hR ε p hε hp
  obtain ⟨η, hηC, hη, hcη, hηrange, hηone, hs, hE⟩ := hCuts M g x R hR
  refine ⟨η, hηC, hη, hcη, hηrange, hηone, hs, ?_⟩
  have hbound := integral_scalar_cutoff_energy_regularized_rpow_bound g hK μ hμ
    hu hunonneg hsub hε hp hη hcη x (show 0 < 3 * R by positivity) hs (A / R) (fun y _ => hE y)
  have hCoeff : 10 * (A / R) ^ 2 = (10 * A ^ 2) / R ^ 2 := by rw [div_pow]; ring
  rw [hCoeff] at hbound
  exact hbound

/-- Genuine annular energy cutoffs for all centers and positive radii,
 with the constant selected before every geometric input. -/
theorem exists_uniform_annular_scalar_energy_cutoffs (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (x : M.Carrier) (r R : ℝ), 0 < r → r < R →
      ∃ η : M.Carrier → ℝ,
        ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
        (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form x y ≤ r → η y = 1) ∧
        tsupport η ⊆ distBall g.form x R ∧
        ∀ y, scalarGradientPair g.form η η y ≤ (C / (R - r)) ^ 2 := by
  obtain ⟨C, hC, hCut⟩ := L12Aux.exists_quantitative_smooth_annular_cutoffs n
  refine ⟨C, hC, ?_⟩
  intro M g x r R hr hrR
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentInnerProductSpace g.form z
  obtain ⟨η, hηC, hη, hcη, hηrange, hηone, hηsupport, hηderiv⟩ := hCut M g x r R hrR
  refine ⟨η, hηC, hη, hcη, hηrange, hηone, ?_, ?_⟩
  · intro y hy
    exact (L12Aux.mem_distBall_iff g x y (hr.trans hrR)).mpr (hηsupport hy)
  · intro y
    apply scalarGradientPair_le_of_realDifferential_bound g.form hη y
      (div_nonneg hC.le (sub_pos.mpr hrR).le)
    change ‖L12Aux.realDifferential g η y‖ ≤ C / (R - r)
    exact hηderiv y

/-- The complete annular Moser energy input is constructed internally.
 The dimensional constant precedes the metric, measure, subharmonic scalar,
 center, both radii, regularization and real iteration exponent. -/
theorem exists_uniform_annular_moser_energy_cutoffs (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsKahler g →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (u : M.Carrier → ℝ), SmoothFn u → (∀ y, 0 ≤ u y) →
        (∀ y, 0 ≤ laplacian g.form u y) → ∀ (x : M.Carrier) (r R : ℝ), 0 < r → r < R →
        ∀ (ε p : ℝ), 0 < ε → 1 ≤ p →
        ∃ η : M.Carrier → ℝ,
          ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ η ∧ SmoothFn η ∧ HasCompactSupport η ∧
          (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧
          (∀ y, inducedDistance g.form x y ≤ r → η y = 1) ∧
          tsupport η ⊆ distBall g.form x R ∧
          (∫ y, scalarGradientPair g.form (fun z => η z * (u z + ε) ^ p)
            (fun z => η z * (u z + ε) ^ p) y ∂μ) ≤
              C / (R - r) ^ 2 * ∫ y in distBall g.form x R, (u y + ε) ^ (2 * p) ∂μ := by
  obtain ⟨A, hA, hCuts⟩ := exists_uniform_annular_scalar_energy_cutoffs n
  refine ⟨10 * A ^ 2, by positivity, ?_⟩
  intro M g hK μ hμ u hu hunonneg hsub x r R hr hrR ε p hε hp
  obtain ⟨η, hηC, hη, hcη, hηrange, hηone, hs, hE⟩ := hCuts M g x r R hr hrR
  refine ⟨η, hηC, hη, hcη, hηrange, hηone, hs, ?_⟩
  have hbound := integral_scalar_cutoff_energy_regularized_rpow_bound g hK μ hμ
    hu hunonneg hsub hε hp hη hcη x (hr.trans hrR) hs (A / (R - r)) (fun y _ => hE y)
  have hCoeff : 10 * (A / (R - r)) ^ 2 = (10 * A ^ 2) / (R - r) ^ 2 := by rw [div_pow]; ring
  rw [hCoeff] at hbound
  exact hbound

/-- An average on any nonnull subset differs from a constant by at most
 its inverse volume times the full absolute-deviation integral. -/
theorem abs_restricted_average_sub_le_integral_abs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Set X) (hs0 : μ s ≠ 0)
    {f : X → ℝ} (hf : Integrable f μ) (c : ℝ) :
    |(μ.real s)⁻¹ * (∫ x in s, f x ∂μ) - c| ≤
      (μ.real s)⁻¹ * ∫ x, |f x - c| ∂μ := by
  have hs0' : (μ.restrict s) univ ≠ 0 := by
    simpa only [Measure.restrict_apply_univ] using hs0
  have hp := abs_average_sub_le_average_abs (μ.restrict s) hs0' hf.integrableOn c
  simp only [Measure.real, Measure.restrict_apply_univ] at hp
  have hAbs : Integrable (fun x => |f x - c|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub (integrable_const c)).norm
  have hmono : (∫ x in s, |f x - c| ∂μ) ≤ ∫ x, |f x - c| ∂μ :=
    setIntegral_le_integral hAbs (ae_of_all μ (fun x => abs_nonneg _))
  exact hp.trans (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr ENNReal.toReal_nonneg))

/-- The difference of the genuine averages on nested original balls is
 controlled by the actual mean oscillation on the outer ball. Positivity,
 finite volume and all restrictions are derived internally. -/
theorem abs_distBall_nested_averages_le_oscillation {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    |(μ.real (distBall g.form x r))⁻¹ * (∫ y in distBall g.form x r, u y ∂μ) -
      (μ.real (distBall g.form x R))⁻¹ * (∫ y in distBall g.form x R, u y ∂μ)| ≤
      (μ.real (distBall g.form x r))⁻¹ * ∫ y in distBall g.form x R,
        |u y - (μ.real (distBall g.form x R))⁻¹ * ∫ z in distBall g.form x R, u z ∂μ| ∂μ := by
  have hR : 0 < R := hr.trans_le hrR
  let ν := μ.restrict (distBall g.form x R)
  letI : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using riemannianVolume_distBall_lt_top g μ hμ x hR⟩
  have hAB : distBall g.form x r ⊆ distBall g.form x R := by
    intro y hy
    exact (L12Aux.mem_distBall_iff g x y hR).mpr
      (((L12Aux.mem_distBall_iff g x y hr).mp hy).trans_le hrR)
  have hνA : ν (distBall g.form x r) = μ (distBall g.form x r) := by
    rw [Measure.restrict_apply (L12Aux.measurableSet_distBall g x r), inter_eq_left.mpr hAB]
  have hν0 : ν (distBall g.form x r) ≠ 0 := by
    rw [hνA]
    exact (riemannianVolume_distBall_pos g μ hμ x hr).ne'
  have hRestr : ν.restrict (distBall g.form x r) = μ.restrict (distBall g.form x r) :=
    Measure.restrict_restrict_of_subset hAB
  have hp := abs_restricted_average_sub_le_integral_abs ν (distBall g.form x r) hν0
    (smoothFn_integrableOn_distBall g μ hμ hu x hR)
    ((μ.real (distBall g.form x R))⁻¹ * ∫ z in distBall g.form x R, u z ∂μ)
  simpa only [Measure.real, hνA, hRestr] using hp

/-- A nonnegative number bounded in two ways is bounded by their weighted
 geometric mean, including the zero cases. -/
theorem le_interpolated_of_le_two_bounds {x M A θ : ℝ}
    (hx0 : 0 ≤ x) (hxM : x ≤ M) (hxA : x ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ≤ M ^ θ * A ^ (1 - θ) := by
  calc
    x = x ^ (θ + (1 - θ)) := by rw [show θ + (1 - θ) = (1 : ℝ) by ring, Real.rpow_one]
    _ = x ^ θ * x ^ (1 - θ) := Real.rpow_add_of_nonneg hx0 hθ0 (sub_nonneg.mpr hθ1)
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow hx0 hxM hθ0)
      (Real.rpow_le_rpow hx0 hxA (sub_nonneg.mpr hθ1))
      (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg (hx0.trans hxM) _)

/-- A strictly subcritical interpolation exponent can be chosen from two
 numerical constants before any geometry is introduced. -/
theorem exists_subcritical_interpolation_exponent {q a : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ha : 0 < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ 0 ≤ q * a ^ (1 - θ) ∧ q * a ^ (1 - θ) < 1 := by
  let f : ℝ → ℝ := fun θ => q * a ^ (1 - θ)
  have hc : Continuous f := continuous_const.mul
    ((Real.continuous_const_rpow (ne_of_gt ha)).comp (continuous_const.sub continuous_id))
  have h1 : f 1 < 1 := by simpa only [f, sub_self, Real.rpow_zero, mul_one] using hq1
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt hc continuous_const).mem_nhds h1)
  let ε := min (δ / 2) (1 / 2 : ℝ)
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨1 - ε, sub_pos.mpr hε1, by linarith, mul_nonneg hq0 (Real.rpow_nonneg ha.le _), ?_⟩
  change f (1 - ε) < 1
  apply hδsub
  change dist (1 - ε) 1 < δ
  rw [Real.dist_eq, show (1 - ε) - 1 = -ε by ring, abs_neg, abs_of_nonneg hε.le]
  exact hεδ

/-- The discrete subcritical potential estimate from actual convergent
 averages. Interpolation makes its dyadic majorant a summable geometric
 series, so no optimized radius choice or maximal-function measurability
 hypothesis is needed. -/
theorem interpolated_geometric_telescoping_bound {q a θ C M A L : ℝ}
    (hq0 : 0 ≤ q) (ha0 : 0 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hρ1 : q * a ^ (1 - θ) < 1) (hC0 : 0 ≤ C) (hM0 : 0 ≤ M) (hA0 : 0 ≤ A)
    (s b : ℕ → ℝ) (hb0 : ∀ k, 0 ≤ b k) (hbM : ∀ k, b k ≤ M)
    (hbA : ∀ k, b k ≤ A * a ^ k)
    (hdiff : ∀ k, |s (k + 1) - s k| ≤ C * q ^ k * b k)
    (hlim : Tendsto s atTop (𝓝 L)) :
    |L - s 0| ≤ C * M ^ θ * A ^ (1 - θ) / (1 - q * a ^ (1 - θ)) := by
  let ρ := q * a ^ (1 - θ)
  let K := C * M ^ θ * A ^ (1 - θ)
  have hρ0 : 0 ≤ ρ := mul_nonneg hq0 (Real.rpow_nonneg ha0 _)
  have hstep (k : ℕ) : dist (s k) (s (k + 1)) ≤ K * ρ ^ k := by
    have hp : (a ^ k) ^ (1 - θ) = (a ^ (1 - θ)) ^ k := by
      rw [← Real.rpow_natCast_mul ha0 k (1 - θ), mul_comm (k : ℝ) (1 - θ),
        Real.rpow_mul_natCast ha0 (1 - θ) k]
    have hb := le_interpolated_of_le_two_bounds (hb0 k) (hbM k) (hbA k) hθ0 hθ1
    rw [Real.mul_rpow hA0 (pow_nonneg ha0 k), hp] at hb
    calc
      _ ≤ C * q ^ k * b k := by simpa only [Real.dist_eq, abs_sub_comm] using hdiff k
      _ ≤ C * q ^ k * (M ^ θ * (A ^ (1 - θ) * (a ^ (1 - θ)) ^ k)) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hC0 (pow_nonneg hq0 k))
      _ = _ := by dsimp [K, ρ]; rw [mul_pow]; ring
  have hsum : HasSum (fun k : ℕ => K * ρ ^ k) (K / (1 - ρ)) := by
    simpa only [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left K
  have hd := dist_le_tsum_of_dist_le_of_tendsto₀ (fun k : ℕ => K * ρ ^ k) hstep hsum.summable hlim
  rw [hsum.tsum_eq] at hd
  simpa only [Real.dist_eq, abs_sub_comm] using hd

end Yau.LeafProofs.L18Aux
