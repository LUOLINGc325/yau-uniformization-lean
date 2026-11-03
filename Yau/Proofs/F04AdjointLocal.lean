import Yau.Proofs.F04Source

/-!
Local Kähler Green calculus for a smooth Hermitian field. The calculation
extracts the local proofs from native L18 and uses only MetricSmooth and
KahlerClosed; it does not require a complete distance for the field.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
set_option maxHeartbeats 1000000

namespace Yau.F04Proof.Adjoint

open Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem realMetricInChart_smooth (g : HermitianField M) (hg : MetricSmooth g)
    (x : M.Carrier) :
    ContDiffOn ℝ ∞ (LeafProofs.L12Aux.realMetricInChart g x) (chartTarget x) := by
  apply LeafProofs.L12Aux.contDiffOn_realBilin_of_basis
  intro a b
  apply (hg x a b).congr
  intro z hz
  exact (LeafProofs.L12Aux.underlyingRealRiemannianMetric_frame g x z hz a b)

theorem hMat_inverse_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => (hMat g x z)⁻¹ i j) (chartTarget x) :=
  contDiffOn_matrix_inv (F04Proof.hMat_contDiffOn_of_metricSmooth g hg x)
    (fun z hz => ne_of_gt (hMat_posDef g x z hz).det_pos) i j

theorem realMetricFn_inverse_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) (a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => (realMetricFn g x z)⁻¹ a b) (chartTarget x) := by
  apply contDiffOn_matrix_inv (hg x)
  intro z hz
  rw [realMetricFn_det g x hz]
  exact pow_ne_zero _ (mul_ne_zero (by norm_num) (ne_of_gt (hMat_det_re_pos g x hz)))

theorem volumeDensity_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => Real.sqrt (realMetricFn g x z).det) (chartTarget x) := by
  have hd : ContDiffOn ℝ ∞ (fun z => (hMat g x z).det.re) (chartTarget x) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (contDiffOn_matrix_det (F04Proof.hMat_contDiffOn_of_metricSmooth g hg x))
  exact (contDiffOn_const.mul hd).congr fun z hz => paperVolumeNormalization g x z hz

theorem scalarMetricFlux_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) (a : RIdx n) :
    ContDiffOn ℝ ∞ (scalarMetricFlux g x u a) (chartTarget x) := by
  apply (volumeDensity_contDiffOn g hg x).mul
  apply ContDiffOn.sum
  intro b _
  exact (realMetricFn_inverse_contDiffOn g hg x a b).mul
    (rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x) (hu x) b)

theorem integral_scalarMetricFlux {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * (∑ a, rDeriv (scalarMetricFlux g x u a) z a) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * scalarMetricFlux g x u a z ∂lebesgueC n) := by
  let _ : (lebesgueC n).IsAddHaarMeasure := by
    rw [LeafProofs.lebesgueC_eq_volume]
    infer_instance
  exact integral_compactTest_divergence_on (lebesgueC n)
    (isOpen_extChartAt_target (I := ComplexModel n) x) hφ hcφ hφO
    (scalarMetricFlux g x u)
    (fun a => (scalarMetricFlux_contDiffOn g hg hu x a).of_le (by simp)) realVec

theorem realMetricFn_differentiableAt {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    DifferentiableAt ℝ (fun w => realMetricFn g x w a b) z :=
  ((hg x a b).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt
      (by simp)

theorem rDeriv_realMetricFn_jIndex {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun w => realMetricFn g x w (jIndex n b) (jIndex n c)) z a =
      jSign b * jSign c * rDeriv (fun w => realMetricFn g x w b c) z a := by
  have heq : (fun w => realMetricFn g x w (jIndex n b) (jIndex n c)) =
      (fun w => (jSign b * jSign c) * realMetricFn g x w b c) := by
    funext w
    exact realMetricFn_jIndex g x w b c
  rw [heq]
  exact rDeriv_const_mul (realMetricFn_differentiableAt g hg x hz b c) _ a

theorem fderiv_volumeDensity {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    fderiv ℝ (fun w => Real.sqrt (realMetricFn g x w).det) z v =
      (Real.sqrt (realMetricFn g x z).det / 2) *
        Matrix.trace ((realMetricFn g x z)⁻¹ *
          (Matrix.of fun a b => fderiv ℝ (fun w => realMetricFn g x w a b) z v)) := by
  have hGd (a b : RIdx n) :
      DifferentiableAt ℝ (fun w => realMetricFn g x w a b) z :=
    realMetricFn_differentiableAt g hg x hz a b
  have hdetd : DifferentiableAt ℝ (fun w => (realMetricFn g x w).det) z :=
    ((contDiffOn_matrix_det (hg x)).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hρ : 0 < Real.sqrt (realMetricFn g x z).det := by
    rw [paperVolumeNormalization g x z hz]
    exact mul_pos (by positivity) (hMat_det_re_pos g x hz)
  have hdet : 0 < (realMetricFn g x z).det := by
    rw [realMetricFn_det g x hz]
    exact sq_pos_of_pos (mul_pos (by positivity) (hMat_det_re_pos g x hz))
  rw [fderiv_sqrt hdetd (ne_of_gt hdet)]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_matrix_det_trace hGd (ne_of_gt hdet)]
  simp_rw [fderiv_matrix_row_apply hGd]
  have hc : (1 / (2 * Real.sqrt (realMetricFn g x z).det)) *
      (realMetricFn g x z).det = Real.sqrt (realMetricFn g x z).det / 2 := by
    field_simp
    nlinarith [Real.sq_sqrt hdet.le]
  rw [← mul_assoc, hc]

theorem rDeriv_density_inverse_entry {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun w => Real.sqrt (realMetricFn g x w).det *
      (realMetricFn g x w)⁻¹ a b) z c =
      (Real.sqrt (realMetricFn g x z).det / 2) *
        Matrix.trace ((realMetricFn g x z)⁻¹ *
          (Matrix.of fun p q => rDeriv (fun w => realMetricFn g x w p q) z c)) *
            (realMetricFn g x z)⁻¹ a b -
      Real.sqrt (realMetricFn g x z).det *
        (((realMetricFn g x z)⁻¹ *
          (Matrix.of fun p q => rDeriv (fun w => realMetricFn g x w p q) z c) *
            (realMetricFn g x z)⁻¹) a b) := by
  have hρd : DifferentiableAt ℝ (fun w => Real.sqrt (realMetricFn g x w).det) z :=
    ((volumeDensity_contDiffOn g hg x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hId : DifferentiableAt ℝ (fun w => (realMetricFn g x w)⁻¹ a b) z :=
    ((realMetricFn_inverse_contDiffOn g hg x a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hdet : ∀ w ∈ chartTarget x, (realMetricFn g x w).det ≠ 0 := by
    intro w hw
    rw [realMetricFn_det g x hw]
    exact pow_ne_zero _ (mul_ne_zero (by norm_num) (ne_of_gt (hMat_det_re_pos g x hw)))
  unfold rDeriv
  rw [fderiv_fun_mul hρd hId]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_volumeDensity g hg x hz,
    fderiv_matrix_inv_entry (isOpen_extChartAt_target (I := ComplexModel n) x)
      (hg x) hdet hz]
  ring

theorem chartKahlerBilin_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartKahlerBilin g x) (chartTarget x) :=
  (realMetricInChart_smooth g hg x).clm_comp contDiffOn_const

theorem fderiv_chartKahlerBilin_realVec {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    fderiv ℝ (chartKahlerBilin g x) z (realVec a) (realVec b) (realVec c) =
      rDeriv (fun t => kahlerFormFn g x t b c) z a := by
  have hB : DifferentiableAt ℝ (chartKahlerBilin g x) z :=
    ((chartKahlerBilin_contDiffOn g hg x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun t => chartKahlerBilin g x t (realVec b) (realVec c)) =ᶠ[𝓝 z]
      (fun t => kahlerFormFn g x t b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with t ht
    exact chartKahlerBilin_realVec g x ht b c
  rw [← fderiv_bilin_apply_const hB]
  exact congrArg (fun A => A (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))

theorem cyclic_chartKahlerBilin_center {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (x : M.Carrier) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin g x) (chartPt x x) u v w +
      fderiv ℝ (chartKahlerBilin g x) (chartPt x x) v w u +
      fderiv ℝ (chartKahlerBilin g x) (chartPt x x) w u v = 0 := by
  apply cyclic_trilinear_zero_of_basis (LeafProofs.complexVector_realOrthonormalBasis n).toBasis
    (fderiv ℝ (chartKahlerBilin g x) (chartPt x x)) _ u v w
  intro a b c
  change fderiv ℝ (chartKahlerBilin g x) (chartPt x x)
    (LeafProofs.complexVector_realOrthonormalBasis n a) (LeafProofs.complexVector_realOrthonormalBasis n b)
      (LeafProofs.complexVector_realOrthonormalBasis n c) +
    fderiv ℝ (chartKahlerBilin g x) (chartPt x x)
      (LeafProofs.complexVector_realOrthonormalBasis n b) (LeafProofs.complexVector_realOrthonormalBasis n c)
        (LeafProofs.complexVector_realOrthonormalBasis n a) +
    fderiv ℝ (chartKahlerBilin g x) (chartPt x x)
      (LeafProofs.complexVector_realOrthonormalBasis n c) (LeafProofs.complexVector_realOrthonormalBasis n a)
        (LeafProofs.complexVector_realOrthonormalBasis n b) = 0
  simp only [LeafProofs.complexVector_realOrthonormalBasis_apply]
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [fderiv_chartKahlerBilin_realVec g hg x hz,
    fderiv_chartKahlerBilin_realVec g hg x hz,
    fderiv_chartKahlerBilin_realVec g hg x hz]
  exact hK x a b c

theorem cyclic_chartKahlerBilin_on {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin g x) z u v w +
      fderiv ℝ (chartKahlerBilin g x) z v w u +
      fderiv ℝ (chartKahlerBilin g x) z w u v = 0 := by
  let y := chartInv x z
  let T : ComplexVector n → ComplexVector n := fun t => chartPt y (chartInv x t)
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have ht : T z ∈ chartTarget y := mem_extChartAt_target y
  have hT : ContDiffAt ℝ 2 T z :=
    ((chartTransition_contDiffAt x y hz hy).restrict_scalars ℝ).of_le (by simp)
  have hBx : DifferentiableAt ℝ (chartKahlerBilin g x) z :=
    ((chartKahlerBilin_contDiffOn g hg x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hBy : DifferentiableAt ℝ (chartKahlerBilin g y) (T z) :=
    ((chartKahlerBilin_contDiffOn g hg y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds ht)).differentiableAt (by simp)
  have hskew (p q : ComplexVector n) :
      chartKahlerBilin g y (T z) p q = -chartKahlerBilin g y (T z) q p :=
    chartKahlerBilin_skew g y ht p q
  have hi : ContinuousAt (chartInv x) z := continuousAt_extChartAt_symm'' hz
  have hs : ∀ᶠ t in 𝓝 z, chartInv x t ∈ (extChartAt (ComplexModel n) y).source :=
    hi.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds hy)
  have hpull (p q : ComplexVector n) :
      (fun t => chartKahlerBilin g x t p q) =ᶠ[𝓝 z]
        (fun t => chartKahlerBilin g y (T t) (fderiv ℝ T t p) (fderiv ℝ T t q)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz, hs]
      with t htx hty
    exact chartKahlerBilin_pullback g x y htx hty p q
  have hderiv (p q r : ComplexVector n) :
      fderiv ℝ (chartKahlerBilin g x) z p q r =
        fderiv ℝ (fun t => chartKahlerBilin g y (T t)
          (fderiv ℝ T t q) (fderiv ℝ T t r)) z p := by
    rw [← fderiv_bilin_apply_const hBx]
    exact congrArg (fun A => A p) ((hpull q r).fderiv_eq (𝕜 := ℝ))
  rw [hderiv u v w, hderiv v w u, hderiv w u v]
  exact (cyclic_derivative_pullback_bilin hT hBy hskew u v w).trans
    (cyclic_chartKahlerBilin_center g hg hK y
      (fderiv ℝ T z u) (fderiv ℝ T z v) (fderiv ℝ T z w))

theorem kahlerClosed_in_chart {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun t => kahlerFormFn g x t b c) z a +
      rDeriv (fun t => kahlerFormFn g x t c a) z b +
      rDeriv (fun t => kahlerFormFn g x t a b) z c = 0 := by
  have hc := cyclic_chartKahlerBilin_on g hg hK x hz (realVec a) (realVec b) (realVec c)
  rw [fderiv_chartKahlerBilin_realVec g hg x hz,
    fderiv_chartKahlerBilin_realVec g hg x hz, fderiv_chartKahlerBilin_realVec g hg x hz] at hc
  exact hc

theorem kahler_metric_derivative_identity_on {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b d : RIdx n) :
    -rDeriv (fun w => realMetricFn g x w b d) z a +
      jSign b * jSign d * rDeriv
        (fun w => realMetricFn g x w (jIndex n d) a) z (jIndex n b) +
      rDeriv (fun w => realMetricFn g x w a b) z d = 0 := by
  have hk := kahlerClosed_in_chart g hg hK x hz a (jIndex n b) d
  have h1 : (fun w => kahlerFormFn g x w (jIndex n b) d) =
      (fun w => (-jSign b) * realMetricFn g x w b d) := by
    funext w
    exact kahlerFormFn_jIndex_left g x w b d
  have h2 : (fun w => kahlerFormFn g x w d a) =
      (fun w => jSign d * realMetricFn g x w (jIndex n d) a) := by
    funext w
    exact kahlerFormFn_eq_jIndex_metric g x w d a
  have h3 : (fun w => kahlerFormFn g x w a (jIndex n b)) =
      (fun w => jSign b * realMetricFn g x w a b) := by
    funext w
    exact kahlerFormFn_jIndex_right g x w a b
  change rDeriv _ z a + rDeriv _ z (jIndex n b) +
    rDeriv _ z d = 0 at hk
  have hG (p q : RIdx n) :
      DifferentiableAt ℝ (fun w => realMetricFn g x w p q) z :=
    realMetricFn_differentiableAt g hg x hz p q
  rw [h1, h2, h3,
    rDeriv_const_mul (hG b d) (-jSign b) a,
    rDeriv_const_mul (hG (jIndex n d) a) (jSign d) (jIndex n b),
    rDeriv_const_mul (hG a b) (jSign b) d] at hk
  by_cases hb : b.2 = 0
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith

theorem kahler_metric_derivative_trace_on {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (d : RIdx n) :
    2 * (∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
      rDeriv (fun w => realMetricFn g x w b d) z a) =
      ∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
        rDeriv (fun w => realMetricFn g x w a b) z d := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g x z)⁻¹
  let D : RIdx n → RIdx n → RIdx n → ℝ := fun a b c =>
    rDeriv (fun w => realMetricFn g x w b c) z a
  have hJA (a b : RIdx n) : A (jIndex n a) (jIndex n b) = jSign a * jSign b * A a b := by
    simpa only [A, chartPt] using
      realMetricFn_inverse_jIndex g x hz a b
  have hJD (a b c : RIdx n) : D a (jIndex n b) (jIndex n c) = jSign b * jSign c * D a b c :=
    rDeriv_realMetricFn_jIndex g hg x hz a b c
  have hSA (a b : RIdx n) : A b a = A a b := by
    simpa only [A] using (realMetricFn_isSymm g x z).inv.apply a b
  have hSD (a b c : RIdx n) : D a b c = D a c b :=
    rDeriv_realMetricFn_symm g x z a b c
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
        kahler_metric_derivative_identity_on g hg hK x hz a b d]
      exact mul_zero _
    simpa only [T, U, S, mul_add, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, mul_assoc] using hzero
  have hfinal : 2 * T = S := by linarith
  simpa only [T, S, A, D] using hfinal

theorem kahler_density_inverse_divergence_on {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (b : RIdx n) :
    (∑ a, rDeriv (fun w => Real.sqrt (realMetricFn g x w).det *
      (realMetricFn g x w)⁻¹ a b) z a) = 0 := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g x z)⁻¹
  let D : RIdx n → Matrix (RIdx n) (RIdx n) ℝ := fun c =>
    Matrix.of fun p q => rDeriv (fun w => realMetricFn g x w p q) z c
  let ρ := Real.sqrt (realMetricFn g x z).det
  let T : RIdx n → ℝ := fun c => ∑ a, ∑ p, A a p * D a p c
  have hD (c p q : RIdx n) : D c p q = D c q p :=
    rDeriv_realMetricFn_symm g x z c p q
  have htrace (c : RIdx n) : Matrix.trace (A * D c) = 2 * T c := by
    calc
      Matrix.trace (A * D c) = ∑ a, ∑ p, A a p * D c a p := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro p _
        rw [hD c p a]
      _ = 2 * T c := (kahler_metric_derivative_trace_on g hg hK x hz c).symm
  have hsum : (∑ a, rDeriv (fun w => Real.sqrt (realMetricFn g x w).det *
      (realMetricFn g x w)⁻¹ a b) z a) =
      (∑ a, (ρ / 2 * Matrix.trace (A * D a) * A a b -
        ρ * ((A * D a * A) a b))) := by
    apply Finset.sum_congr rfl
    intro a _
    exact rDeriv_density_inverse_entry g hg x hz a b a
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

theorem kahler_scalarMetricFlux_divergence_on {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    (∑ a, rDeriv (scalarMetricFlux g x u a) z a) =
      2 * Real.sqrt (realMetricFn g x z).det * traceWith (hMat g x z) (leviC (inChart x u) z) := by
  let ρ := Real.sqrt (realMetricFn g x z).det
  let B : RIdx n → RIdx n → ComplexVector n → ℝ := fun a b w =>
    Real.sqrt (realMetricFn g x w).det * (realMetricFn g x w)⁻¹ a b
  have hB (a b : RIdx n) : DifferentiableAt ℝ (B a b) z :=
    (((volumeDensity_contDiffOn g hg x).mul
      (realMetricFn_inverse_contDiffOn g hg x a b)).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hf : ContDiffAt ℝ 2 (inChart x u) z :=
    ((hu x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hflux (a : RIdx n) : scalarMetricFlux g x u a =
      (fun w => ∑ b, B a b w * rDeriv (inChart x u) w b) := by
    funext w
    simp only [scalarMetricFlux, B, Finset.mul_sum, mul_assoc]
  have hfirst : (∑ b, (∑ a, rDeriv (B a b) z a) * rDeriv (inChart x u) z b) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    have hzero : (∑ a, rDeriv (B a b) z a) = 0 :=
      kahler_density_inverse_divergence_on g hg hK x hz b
    rw [hzero, zero_mul]
  have hstart : (∑ a, rDeriv (scalarMetricFlux g x u a) z a) =
      (∑ a, rDeriv (fun w => ∑ b, B a b w * rDeriv (inChart x u) w b) z a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hflux]
  rw [hstart, divergence_matrix_gradient B hB hf, hfirst, zero_add]
  calc
    (∑ a, ∑ b, B a b z *
      fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) =
        ρ * (∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
          fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change (ρ * (realMetricFn g x z)⁻¹ a b) * _ =
        ρ * ((realMetricFn g x z)⁻¹ a b * _)
      ring
    _ = ρ * (2 * traceWith (hMat g x z) (leviC (inChart x u) z)) :=
      congrArg (fun q => ρ * q)
        (principal_realLaplacian_eq_twice_traceWith g x hz hf)
    _ = 2 * Real.sqrt (realMetricFn g x z).det * traceWith (hMat g x z) (leviC (inChart x u) z) := by
      change ρ * (2 * traceWith (hMat g x z) (leviC (inChart x u) z)) = 2 * ρ * traceWith (hMat g x z) (leviC (inChart x u) z)
      ring

theorem integral_kahler_chart_trace {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * (2 * Real.sqrt (realMetricFn g x z).det *
      traceWith (hMat g x z) (leviC (inChart x u) z)) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * scalarMetricFlux g x u a z ∂lebesgueC n) := by
  have heq : (fun z => φ z * (∑ a, rDeriv (scalarMetricFlux g x u a) z a)) =
      (fun z => φ z * (2 * Real.sqrt (realMetricFn g x z).det *
        traceWith (hMat g x z) (leviC (inChart x u) z))) := by
    funext z
    by_cases hzero : φ z = 0
    · simp only [hzero, zero_mul]
    · have hz : z ∈ chartTarget x := hφO (subset_closure hzero)
      rw [kahler_scalarMetricFlux_divergence_on g hg hK hu x hz]
  rw [← heq]
  exact integral_scalarMetricFlux g hg hu x hφ hcφ hφO

theorem integral_kahler_laplacian {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (x : M.Carrier) {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * (2 * Real.sqrt (realMetricFn g x z).det *
      laplacian g u (chartInv x z)) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * scalarMetricFlux g x u a z ∂lebesgueC n) := by
  have heq : (fun z => φ z * (2 * Real.sqrt (realMetricFn g x z).det *
      traceWith (hMat g x z) (leviC (inChart x u) z))) =
    (fun z => φ z * (2 * Real.sqrt (realMetricFn g x z).det *
      laplacian g u (chartInv x z))) := by
    funext z
    by_cases hzero : φ z = 0
    · simp only [hzero, zero_mul]
    · rw [traceWith_inChart_eq_laplacian g hu x (hφO (subset_closure hzero))]
  rw [← heq]
  exact integral_kahler_chart_trace g hg hK hu x hφ hcφ hφO

end Yau.F04Proof.Adjoint
