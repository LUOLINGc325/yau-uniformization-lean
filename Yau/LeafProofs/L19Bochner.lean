import Yau.LeafProofs.L19Evolution
import Yau.LeafProofs.L12JacobiCalculus

/-! Actual coordinate tensors for the Bochner argument. All metric,
connection, and curvature coefficients are the pre-existing calculators. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The true scalar covariant Hessian in one fixed real coordinate frame. -/
def chartCovHessian (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun i j => rDeriv (fun w => rDeriv f w j) z i -
    ∑ k, christoffel h a z k i j * rDeriv f z k

/-- The independently displayed real Levi--Civita scalar Laplacian. -/
def chartRealLaplacian (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  ∑ i, ∑ j, (realMetricFn h a z)⁻¹ i j * chartCovHessian h a f z i j

theorem chartCovHessian_symm (h : HermitianField M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) :
    (chartCovHessian h a f z).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, chartCovHessian,
    rDeriv_rDeriv_eq_hessian hf]
  rw [hf.isSymmSndFDerivAt (by norm_num) (realVec j) (realVec i)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [L12Aux.christoffel_symm_lower]

/-- Inverse metric compatibility, proved by differentiating the actual
matrix inverse and the actual metric compatibility identity once. -/
theorem inverseMetric_directional_derivative (g : SmoothMetric M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (k : RIdx n) :
    L12Aux.matrixDirectionalDerivative (fun w => (realMetricFn g.form a w)⁻¹) z
        (realVec k) =
      -(L12Aux.connectionMatrix g.form a z k * (realMetricFn g.form a z)⁻¹ +
        (realMetricFn g.form a z)⁻¹ * (L12Aux.connectionMatrix g.form a z k)ᵀ) := by
  let G := realMetricFn g.form a z
  let C := L12Aux.connectionMatrix g.form a z k
  have hunit : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef g.form a z hz).det_pos.ne'
  have hGA : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hunit
  have hAG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit
  have hd := L12Aux.matrixDirectionalDerivative_inv
    (fun i j => realMetricFn_differentiableAt g a hz i j)
    (L12Aux.realMetricFn_posDef g.form a z hz).det_pos.ne' (realVec k)
  rw [L12Aux.metricDirectionalDerivative_eq_connection g a z hz k] at hd
  change L12Aux.matrixDirectionalDerivative (fun w => (realMetricFn g.form a w)⁻¹)
      z (realVec k) = -(C * G⁻¹ + G⁻¹ * Cᵀ)
  rw [hd]
  change -(G⁻¹ * (Cᵀ * G + G * C) * G⁻¹) = _
  congr 1
  calc
    _ = G⁻¹ * Cᵀ * (G * G⁻¹) + (G⁻¹ * G) * C * G⁻¹ := by noncomm_ring
    _ = _ := by rw [hGA, hAG]; simp only [Matrix.mul_one, Matrix.one_mul]; abel

theorem inverseMetric_derivative_connection (g : SmoothMetric M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (k i j : RIdx n) :
    rDeriv (fun w => (realMetricFn g.form a w)⁻¹ i j) z k =
      -(∑ p, christoffel g.form a z i k p * (realMetricFn g.form a z)⁻¹ p j) -
        ∑ p, christoffel g.form a z j k p * (realMetricFn g.form a z)⁻¹ i p := by
  have hd := congrArg (fun B : Matrix (RIdx n) (RIdx n) ℝ => B i j)
    (inverseMetric_directional_derivative g a hz k)
  simpa only [L12Aux.matrixDirectionalDerivative, rDeriv, Matrix.neg_apply,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, L12Aux.connectionMatrix,
    neg_add_rev, neg_add, sub_eq_add_neg, mul_comm, add_comm] using hd

/-- The vanishing Christoffel contraction is valid throughout every
fixed holomorphic chart, not just at its center. -/
theorem kahler_christoffel_trace_on (g : SmoothMetric M) (hK : IsKahler g)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (c : RIdx n) :
    (∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b * christoffel g.form x z c a b) = 0 := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form x z)⁻¹
  let D : RIdx n → RIdx n → RIdx n → ℝ := fun a b d =>
    rDeriv (fun w => realMetricFn g.form x w b d) z a
  have hSA (a b : RIdx n) : A b a = A a b :=
    (realMetricFn_isSymm g.form x z).inv.apply a b
  have hzero (d : RIdx n) :
      (∑ a, ∑ b, A a b * (D a b d + D b a d - D d a b)) = 0 := by
    have hT : 2 * (∑ a, ∑ b, A a b * D a b d) =
        ∑ a, ∑ b, A a b * D d a b := kahler_metric_derivative_trace_on g hK x hz d
    have hswap : (∑ a, ∑ b, A a b * D b a d) = ∑ a, ∑ b, A a b * D a b d := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
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
      intro d hd
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = 0 := by simp only [hzero, mul_zero, Finset.sum_const_zero]

theorem chartRealLaplacian_eq_principal (g : SmoothMetric M) (hK : IsKahler g)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (f : ComplexVector n → ℝ) :
    chartRealLaplacian g.form a f z =
      ∑ i, ∑ j, (realMetricFn g.form a z)⁻¹ i j *
        rDeriv (fun w => rDeriv f w j) z i := by
  unfold chartRealLaplacian chartCovHessian
  simp only [mul_sub, Finset.sum_sub_distrib]
  suffices hzero : (∑ i, ∑ j, (realMetricFn g.form a z)⁻¹ i j *
      ∑ k, christoffel g.form a z k i j * rDeriv f z k) = 0 by rw [hzero, sub_zero]
  simp only [Finset.mul_sum]
  rw [sum_three_cycle]
  have heq (k : RIdx n) : (∑ i, ∑ j, (realMetricFn g.form a z)⁻¹ i j *
      (christoffel g.form a z k i j * rDeriv f z k)) =
      (∑ i, ∑ j, (realMetricFn g.form a z)⁻¹ i j * christoffel g.form a z k i j) *
        rDeriv f z k := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [heq, kahler_christoffel_trace_on g hK a hz, zero_mul]
  simp

/-- The real operator in any fixed chart computes twice the original
intrinsic complex Laplacian on the entire chart target. -/
theorem kahler_realLaplacian_on (g : SmoothMetric M) (hK : IsKahler g)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    chartRealLaplacian g.form a (inChart a f) z =
      2 * laplacian g.form f (chartInv a z) := by
  rw [chartRealLaplacian_eq_principal g hK a hz]
  have htwo : ContDiffAt ℝ 2 (inChart a f) z := (contDiffAt_inChart hf a hz).of_le (by simp)
  simp_rw [rDeriv_rDeriv_eq_hessian htwo]
  rw [principal_realLaplacian_eq_twice_traceWith g.form a hz htwo,
    traceWith_inChart_eq_laplacian g.form hf a hz]

/-- The local gradient drift obeys Cauchy--Schwarz for the inverse of the
actual positive definite real metric. No smoothness hypothesis is needed. -/
theorem chartGradientPair_cauchySchwarz (h : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (f k : ComplexVector n → ℝ) :
    chartGradientPair h a f k z ^ 2 ≤
      chartGradientPair h a f f z * chartGradientPair h a k k z := by
  have hp := (L12Aux.realMetricFn_posDef h a z hz).inv.star_dotProduct_mulVec_mul_le
    (fun i => rDeriv f z i) (fun i => rDeriv k z i)
  simpa only [chartGradientPair, Matrix.toBilin'_apply', star_trivial, pow_two] using hp

end Yau.LeafProofs.L19Aux
