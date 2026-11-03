import Yau.Proofs.C04BisectionalScalarUnitBound

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Proofs.C04BisectionalScalarAux
open Yau Yau.Blueprint Yau.NodeProofs Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem curvatureValue_alternation (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (U V W Z : Fin n → ℂ) :
    (∑ k, ∑ l, (∑ j, ∑ i, C i j k l * W i * star (Z j)) *
      (U k * star (V l) - V k * star (U l))) =
      curvatureValue C W Z U V - curvatureValue C W Z V U := by
  unfold curvatureValue
  rw [P06Aux.scalarUniqueness_sum_four_exchange
    (fun i j a b => C i j a b * W i * star (Z j) * U a * star (V b)),
    P06Aux.scalarUniqueness_sum_four_exchange
      (fun i j a b => C i j a b * W i * star (Z j) * V a * star (U b))]
  simp only [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realRm_eq_curvatureValue (k : HermitianField M) (hs : MetricSmooth k)
    (hk : KahlerClosed k) (x : M.Carrier) (U V W Z : ComplexVector n) :
    G01Aux.realRmInChart k x (chartPt x x) U V W Z =
      2*(curvatureValue (chernCurvature k x) (fun i => W i) (fun i => Z i)
        (fun i => U i) (fun i => V i) -
        curvatureValue (chernCurvature k x) (fun i => W i) (fun i => Z i)
        (fun i => V i) (fun i => U i)).re := by
  rw [G01Aux.realRmInChart_eq_chern k hs hk x (chartPt x x)
      (show chartPt x x ∈ chartTarget x from mem_extChartAt_target x),
    curvatureValue_alternation]
  rfl

theorem realRm_unit_bound (k : HermitianField M) (hs : MetricSmooth k)
    (hk : KahlerClosed k) (hBC : NonnegBisectional k) (x : M.Carrier)
    (U V W Z : ComplexVector n)
    (hu : metricQuadratic (gMat k x) (fun i => U i) ≤ 1)
    (hv : metricQuadratic (gMat k x) (fun i => V i) ≤ 1)
    (hw : metricQuadratic (gMat k x) (fun i => W i) ≤ 1)
    (hz : metricQuadratic (gMat k x) (fun i => Z i) ≤ 1) :
    |G01Aux.realRmInChart k x (chartPt x x) U V W Z| ≤ 64*scalarCurvature k x := by
  have ha := chernCurvature_unit_bound k hs hk hBC x _ _ _ _ hw hz hu hv
  have hb := chernCurvature_unit_bound k hs hk hBC x _ _ _ _ hw hz hv hu
  rw [realRm_eq_curvatureValue k hs hk]
  have hh := (Complex.abs_re_le_norm _).trans
    ((norm_sub_le _ _).trans (add_le_add ha hb))
  rw [abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
  nlinarith

theorem metricQuadratic_real_coords (k : HermitianField M) (x : M.Carrier)
    (U : ComplexVector n) :
    2*metricQuadratic (gMat k x) (fun i => U i) =
      realCoord U ⬝ᵥ (realMetricFn k x (chartPt x x) *ᵥ realCoord U) := by
  rw [G01Aux.realMetricFn_eq_rawReal, ← G01Aux.hermitianRealification_eq]
  simpa only [L12Aux.complexCoordsOfReal_realCoord, star_trivial, metricQuadratic, gMat]
    using (L12Aux.hermitianRealification_quadratic (gMat k x) (realCoord U)).symm

theorem tensorEvaluation_rm_eq (k : HermitianField M) (x : M.Carrier)
    (U V W Z : ComplexVector n) :
    L23Aux.tensorEvaluation (rmTensor k x (chartPt x x))
      ![realCoord U,realCoord V,realCoord W,realCoord Z] =
      G01Aux.realRmInChart k x (chartPt x x) U V W Z := by
  rw [L23Aux.tensorEvaluation_four]
  simp only [G01Aux.realRmInChart, rmTensor, L12Aux.curvature4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

end Yau.Proofs.C04BisectionalScalarAux
