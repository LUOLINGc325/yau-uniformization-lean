import Yau.Proofs.G01RicciLocal
import Yau.Proofs.G01Realification
import Yau.Proofs.G01ScalarNaturality
import Yau.LeafProofs.L22LeviBasic
import Yau.LeafProofs.L23RicciBound

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The independently computed real Ricci matrix equals twice the symmetric realification. -/
theorem realRicciCoeff_eq_iota (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    realRicciCoeff h x z a b =
      2 * (Parabolic.iota (Blueprint.ricciInChart h x z) : Parabolic.Mat n) a b := by
  have hf : ContDiffAt ℝ 2 (logDet h x) z :=
    ((L17Aux.logDet_contDiffOn_of_metricSmooth h hs x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hr : (Blueprint.ricciInChart h x z).IsHermitian :=
    (L22Aux.leviC_isHermitian hf).neg
  rw [L23Aux.realRicciCoeff_eq_realRicciMatrix h x z hz,
    realRicciMatrix_eq_realification h hs hk x z hz,
    hermitianRealification_eq, ← Blueprint.ricciInChart,
    rawReal_eq_iota _ hr]
  rfl

/-- A symmetric coefficient contraction is the ordinary product trace. -/
theorem symmetric_contraction_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    (∑ a, ∑ b, A a b * B a b) = Matrix.trace (A * B) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show B b a = B a b from hB.apply a b]

/-- The real scalar calculator has exactly twice the complex trace. -/
theorem realScalarCurvatureInChart_eq_traceWith (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) :
    Blueprint.realScalarCurvatureInChart h x z =
      2 * traceWith (hMat h x z) (Blueprint.ricciInChart h x z) := by
  unfold Blueprint.realScalarCurvatureInChart
  simp_rw [L23Aux.realRicciCoeff_eq_realRicciMatrix h x z hz]
  rw [symmetric_contraction_eq_trace _ _ (by
    ext a b
    exact L23Aux.realRicciMatrix_symm h hs x z hz b a)]
  rw [realMetricFn_inverse_eq h x z hz,
    realRicciMatrix_eq_realification h hs hk x z hz,
    hermitianRealification_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul, ← rawReal_mul,
    rawReal_trace]
  rfl

/-- Every actual chart computes the scalar curvature at the represented manifold point. -/
theorem realScalarCurvatureInChart_eq (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) :
    Blueprint.realScalarCurvatureInChart h x z = 2 * scalarCurvature h (chartInv x z) := by
  rw [realScalarCurvatureInChart_change h hs x (chartInv x z) hz
    (mem_extChartAt_source (chartInv x z))]
  exact realScalarCurvatureInChart_eq_traceWith h hs hk (chartInv x z)
    (chartPt (chartInv x z) (chartInv x z)) (mem_extChartAt_target (chartInv x z))

theorem paperRicciChartNormalization (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) : Blueprint.PaperRicciChartNormalization h :=
  ⟨realRicciCoeff_eq_iota h hs hk, realScalarCurvatureInChart_eq h hs hk⟩

/-- The exact original central-chart Ricci identification, in every complex dimension. -/
theorem kahlerRealRicciIdentification : Blueprint.KahlerRealRicciIdentification := by
  intro n M h hs hk x a b
  exact realRicciCoeff_eq_iota h hs hk x (chartPt x x) (mem_extChartAt_target x) a b

end Yau.NodeProofs.G01Aux
