import Yau.LeafProofs.L21WeightedDomainsSources

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedColumnFn (A : X n → Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (x : X n) : X n :=
  WithLp.toLp 2 (fun j => (rho x : ℂ)*A x j k)

theorem weightedColumn_memLp (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2)) (k : Fin n) :
    MemLp (weightedColumnFn A k) 2 (weightedBallMeasure n K) := by
  apply MemLp.of_eval_piLp
  intro j
  exact weightedDomains_memLp_of_continuousOn_ball_two K hK
    ((Complex.ofRealCLM.continuous.comp contDiff_rho.continuous).continuousOn.mul (hA2 j k).continuousOn)

def weightedColumn (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2)) (k : Fin n) :
    WeightedOneForm n K := (weightedColumn_memLp K hK A hA2 k).toLp (weightedColumnFn A k)

theorem weightedColumn_rep (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2)) (k : Fin n) :
    (weightedColumn K hK A hA2 k : X n → X n) =ᵐ[weightedBallMeasure n K] weightedColumnFn A k :=
  (weightedColumn_memLp K hK A hA2 k).coeFn_toLp

def weightedCoordinate (K : ℝ) (hK : 0 ≤ K) (k : Fin n) : WeightedScalar n K :=
  (weightedDomains_memLp_of_continuousOn_ball_two K hK
    (EuclideanSpace.proj k : X n →L[ℂ] ℂ).continuous.continuousOn).toLp (fun x => x k)

theorem weightedColumn_graph (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2)) (k : Fin n) :
    (weightedCoordinate K hK k,weightedColumn K hK A hA2 k) ∈
      (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).graph := by
  let hA := weightedDomains_matrixSmoothOn_ball_one hA2
  unfold weightedMaximalT
  rw [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (weightedField_eq_zero_of_projections K)]
  apply weightedRowsGraph_of_smooth_representatives K hK _ _ _ _ _ _ _
    (weightedCoordinate K hK k) (weightedColumn K hK A hA2 k) (fun x (_ : Unit) => x k)
  · intro c
    exact ((EuclideanSpace.proj k : X n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.contDiffOn
  · intro c
    exact (weightedDomains_memLp_of_continuousOn_ball_two K hK
      (EuclideanSpace.proj k : X n →L[ℂ] ℂ).continuous.continuousOn).coeFn_toLp.symm
  · intro j
    filter_upwards [weightedColumn_rep K hK A hA2 k,
      weightedFieldProjection_coeFn K j (weightedColumn K hK A hA2 k)] with x hx hy
    rw [hy,hx]
    rw [weightedTSystemApply_eq_degenerateT]
    change (rho x : ℂ)*dbarA A j (fun y => y k) x = (rho x : ℂ)*A x j k
    rw [weightedDomains_dbarA_coordinate]

theorem weightedColumn_norm_sq (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2)) (k : Fin n) :
    ‖weightedColumn K hK A hA2 k‖^2 =
      ∑ j, ∫ x, ‖(rho x : ℂ)*A x j k‖^2 ∂weightedBallMeasure n K := by
  rw [weightedField_norm_sq_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [weightedColumn_rep K hK A hA2 k] with x hx
  rw [hx]
  rfl

end Yau.LeafProofs.L21Aux
