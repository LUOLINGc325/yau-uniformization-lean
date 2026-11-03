import Yau.Proofs.P06IntervalResidual

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

def intervalUpperForm (g : HermitianField M) (C : ℝ) (A : RealForm M 2) :=
  positiveForm g (A - intervalForm g C A)
def intervalLowerForm (g : HermitianField M) (C : ℝ) (A : RealForm M 2) :=
  positiveForm g (-(A - intervalForm g C A))

theorem intervalUpperForm_oneOne (g : HermitianField M) (C : ℝ) (A : RealForm M 2) :
    RealOneOne (intervalUpperForm g C A) := positiveForm_oneOne g _
theorem intervalLowerForm_oneOne (g : HermitianField M) (C : ℝ) (A : RealForm M 2) :
    RealOneOne (intervalLowerForm g C A) := positiveForm_oneOne g _
theorem intervalUpperForm_nonnegative (g : HermitianField M) (C : ℝ) (A : RealForm M 2) :
    FormLE 0 (intervalUpperForm g C A) := positiveForm_nonnegative g _
theorem intervalLowerForm_nonnegative (g : HermitianField M) (C : ℝ) (A : RealForm M 2) :
    FormLE 0 (intervalLowerForm g C A) := positiveForm_nonnegative g _

theorem intervalUpperForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) {C : ℝ} (hC : 0 ≤ C) :
    L2RealForm g.form μ (intervalUpperForm g.form C A) :=
  FiberApprox.positiveForm_l2_of_l2 g μ _
    (l2RealForm_sub g μ A _ hA (FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC))
    (realOneOne_sub A _ h11 (intervalForm_oneOne g.form C A))

theorem intervalLowerForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) {C : ℝ} (hC : 0 ≤ C) :
    L2RealForm g.form μ (intervalLowerForm g.form C A) := by
  have hr := l2RealForm_sub g μ A _ hA (FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC)
  have hn : L2RealForm g.form μ (-(A - intervalForm g.form C A)) := by
    simpa only [zero_sub] using l2RealForm_sub g μ 0 _ (l2RealForm_zero g.form μ) hr
  exact FiberApprox.positiveForm_l2_of_l2 g μ _ hn
    (realOneOne_neg _ (realOneOne_sub A _ h11 (intervalForm_oneOne g.form C A)))

theorem intervalForm_residual_split (g : HermitianField M) (C : ℝ)
    (A : RealForm M 2) (h11 : RealOneOne A) :
    A - intervalForm g C A = intervalUpperForm g C A - intervalLowerForm g C A :=
  positiveForm_split g _ (realOneOne_sub A _ h11 (intervalForm_oneOne g C A))

theorem pointFormHS_interval (g : HermitianField M) (C : ℝ) (A : RealForm M 2) (x : M.Carrier) :
    pointFormHS g (intervalForm g C A) x =
      matrixToHS (matrixIntervalClip C (metricWhiten (gMat g x) (formHermitianMatrix A x))) := by
  rw [pointFormHS, intervalForm_matrix, relativeMatrixHS,
    metricWhiten_relativeIntervalClip C (gMat g x) _
      (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))]

theorem pointFormHS_omega (g : HermitianField M) (x : M.Carrier) :
    pointFormHS g (G04Aux.omegaForm g) x = matrixToHS (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [pointFormHS, G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.omegaForm_represents g),
    relativeMatrixHS, metricWhiten_metric (gMat g x)
      (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))]

theorem pointFormHS_intervalUpper (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier) :
    pointFormHS g (intervalUpperForm g C A) x =
      matrixToHS (matrixUpperResidual C (metricWhiten (gMat g x) (formHermitianMatrix A x))) := by
  rw [intervalUpperForm, pointFormHS_positive, formHermitianMatrix_sub, intervalForm_matrix,
    metricWhiten_sub, metricWhiten_relativeIntervalClip C (gMat g x) _
      (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)),
    matrixUpperResidual_eq_positive hC _ (metricWhiten_hermitian _ _ ((G04Aux.representsSelf A h11).2 x))]

theorem pointFormHS_intervalLower (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier) :
    pointFormHS g (intervalLowerForm g C A) x =
      matrixToHS (matrixLowerResidual C (metricWhiten (gMat g x) (formHermitianMatrix A x))) := by
  rw [intervalLowerForm, pointFormHS_positive, formHermitianMatrix_neg, metricWhiten_neg,
    formHermitianMatrix_sub, intervalForm_matrix, metricWhiten_sub,
    metricWhiten_relativeIntervalClip C (gMat g x) _
      (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))]
  have he : -(metricWhiten (gMat g x) (formHermitianMatrix A x) -
      matrixIntervalClip C (metricWhiten (gMat g x) (formHermitianMatrix A x))) =
      matrixIntervalClip C (metricWhiten (gMat g x) (formHermitianMatrix A x)) -
        metricWhiten (gMat g x) (formHermitianMatrix A x) := by abel
  rw [he, matrixLowerResidual_eq_positive hC _
    (metricWhiten_hermitian _ _ ((G04Aux.representsSelf A h11).2 x))]

theorem formInner_intervalUpper (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier) :
    formInner g (intervalUpperForm g C A) (intervalForm g C A) x =
      C * formTrace g (intervalUpperForm g C A) x := by
  rw [← formInner_omegaForm g _ (intervalUpperForm_oneOne g C A) x,
    formInner_eq_pointFormHS g _ _ (intervalUpperForm_oneOne g C A) (intervalForm_oneOne g C A) x,
    formInner_eq_pointFormHS g _ _ (intervalUpperForm_oneOne g C A) (G04Aux.omegaForm_oneOne g) x,
    pointFormHS_intervalUpper g hC A h11 x, pointFormHS_interval, pointFormHS_omega,
    matrixToHS_inner _ _ (matrixIntervalClip_residual_positive C _).1.1,
    matrixToHS_inner _ _ (matrixIntervalClip_residual_positive C _).1.1, mul_one]
  have hz := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace B).re)
    (matrixIntervalClip_upper_orthogonal C
      (metricWhiten (gMat g x) (formHermitianMatrix A x))
      (metricWhiten_hermitian (gMat g x) (formHermitianMatrix A x) ((G04Aux.representsSelf A h11).2 x)))
  simp only [Matrix.mul_sub, Matrix.mul_smul, mul_one, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Matrix.trace_zero, Complex.zero_re] at hz
  linarith

theorem formInner_intervalLower (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier) :
    formInner g (intervalLowerForm g C A) (intervalForm g C A) x =
      -C * formTrace g (intervalLowerForm g C A) x := by
  rw [← formInner_omegaForm g _ (intervalLowerForm_oneOne g C A) x,
    formInner_eq_pointFormHS g _ _ (intervalLowerForm_oneOne g C A) (intervalForm_oneOne g C A) x,
    formInner_eq_pointFormHS g _ _ (intervalLowerForm_oneOne g C A) (G04Aux.omegaForm_oneOne g) x,
    pointFormHS_intervalLower g hC A h11 x, pointFormHS_interval, pointFormHS_omega,
    matrixToHS_inner _ _ (matrixIntervalClip_residual_positive C _).2.1,
    matrixToHS_inner _ _ (matrixIntervalClip_residual_positive C _).2.1, mul_one]
  have hz := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace B).re)
    (matrixIntervalClip_lower_orthogonal hC
      (metricWhiten (gMat g x) (formHermitianMatrix A x))
      (metricWhiten_hermitian (gMat g x) (formHermitianMatrix A x) ((G04Aux.representsSelf A h11).2 x)))
  simp only [Matrix.mul_add, Matrix.mul_smul, mul_one, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Matrix.trace_zero, Complex.zero_re] at hz
  linarith

end Yau.NodeProofs.P06Aux.Clip
