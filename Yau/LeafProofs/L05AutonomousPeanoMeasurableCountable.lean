import Yau.LeafProofs.L05AutonomousPeanoMeasurableHessian
import Mathlib.Topology.DenseEmbedding

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Only countably many literal inequalities enter this good-set definition. -/
def peanoCountableGoodSet {n : ℕ} (u : Point n → ℝ)
    (G : Point n → (Space n →L[ℝ] ℝ)) : Set (Point n) :=
  {p | ∀ k : ℕ, ∃ m : ℕ, ∀ q : ℕ,
    ‖TopologicalSpace.denseSeq (Space n) q‖ < 1/(m+1 : ℝ) →
      |peanoSpatialRemainder u p (G p) (autoBilinearMap n (peanoMeasurableHessian u p))
        (TopologicalSpace.denseSeq (Space n) q)| ≤
          ‖TopologicalSpace.denseSeq (Space n) q‖^2/(k+1 : ℝ)}

theorem peano_remainder_continuous {n : ℕ} {u : Point n → ℝ} (hu : Continuous u)
    (p : Point n) (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    Continuous (peanoSpatialRemainder u p l B) := by
  unfold peanoSpatialRemainder
  fun_prop

theorem measurable_peano_remainder {n : ℕ} {u : Point n → ℝ} (hu : Continuous u)
    {G : Point n → (Space n →L[ℝ] ℝ)} (hG : Measurable G) (v : Space n) :
    Measurable (fun p => peanoSpatialRemainder u p (G p)
      (autoBilinearMap n (peanoMeasurableHessian u p)) v) := by
  have hShift : Continuous (fun p : Point n => (p.1+v,p.2)) := by fun_prop
  have hGv : Measurable (fun p => G p v) := (ContinuousLinearMap.measurable_apply v).comp hG
  have hB : Measurable (fun p => autoBilinearMap n (peanoMeasurableHessian u p)) :=
    (autoBilinearMap n).continuous.measurable.comp (measurable_peanoMeasurableHessian hu)
  have hBv := (ContinuousLinearMap.measurable_apply v).comp hB
  have hBvv := (ContinuousLinearMap.measurable_apply v).comp hBv
  exact (((hu.comp hShift).measurable.sub hu.measurable).sub hGv).sub (hBvv.const_mul (1/2))

theorem measurableSet_peanoCountableGoodSet {n : ℕ} {u : Point n → ℝ}
    (hu : Continuous u) {G : Point n → (Space n →L[ℝ] ℝ)} (hG : Measurable G) :
    MeasurableSet (peanoCountableGoodSet u G) := by
  classical
  simp only [peanoCountableGoodSet,Set.ofPred_forall,Set.ofPred_exists]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun m =>
    MeasurableSet.iInter fun q => MeasurableSet.iInter fun _hSmall => ?_
  exact measurableSet_le (measurable_peano_remainder hu hG _).abs measurable_const

/-- Density extends each countable small-increment inequality to the entire
open small ball, using continuity only in the increment variable. -/
theorem peano_countable_bound_extension {n : ℕ} {u : Point n → ℝ}
    (hu : Continuous u) (p : Point n) (l : Space n →L[ℝ] ℝ)
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) (k m : ℕ)
    (hDense : ∀ q : ℕ, ‖TopologicalSpace.denseSeq (Space n) q‖ < 1/(m+1 : ℝ) →
      |peanoSpatialRemainder u p l B (TopologicalSpace.denseSeq (Space n) q)| ≤
        ‖TopologicalSpace.denseSeq (Space n) q‖^2/(k+1 : ℝ)) :
    ∀ v : Space n, ‖v‖ < 1/(m+1 : ℝ) →
      |peanoSpatialRemainder u p l B v| ≤ ‖v‖^2/(k+1 : ℝ) := by
  intro v
  have hClosed : IsClosed {w : Space n | ‖w‖ < 1/(m+1 : ℝ) →
      |peanoSpatialRemainder u p l B w| ≤ ‖w‖^2/(k+1 : ℝ)} := by
    simp only [imp_iff_not_or,not_lt,Set.ofPred_or]
    exact (isClosed_le continuous_const continuous_norm).union
      (isClosed_le (peano_remainder_continuous hu p l B).abs
        ((continuous_norm.pow 2).div_const (k+1 : ℝ)))
  exact (TopologicalSpace.denseRange_denseSeq (Space n)).induction_on v hClosed hDense

theorem peano_littleO_of_countable {n : ℕ} {u : Point n → ℝ} (hu : Continuous u)
    {G : Point n → (Space n →L[ℝ] ℝ)} {p : Point n}
    (hp : p ∈ peanoCountableGoodSet u G) :
    (fun y => u (y,p.2)-u p-G p (y-p.1)-
      (1/2 : ℝ)*autoBilinearMap n (peanoMeasurableHessian u p) (y-p.1) (y-p.1))
        =o[𝓝 p.1] (fun y => ‖y-p.1‖^2) := by
  apply IsLittleO.of_bound
  intro c hc
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hc
  obtain ⟨m,hm⟩ := hp k
  have hmPos : 0 < 1/(m+1 : ℝ) := by positivity
  filter_upwards [Metric.ball_mem_nhds p.1 hmPos] with y hy
  have hSmall : ‖y-p.1‖ < 1/(m+1 : ℝ) := by
    simpa only [Metric.mem_ball,dist_eq_norm] using hy
  have hBound := peano_countable_bound_extension hu p (G p)
    (autoBilinearMap n (peanoMeasurableHessian u p)) k m hm (y-p.1) hSmall
  simp only [peanoSpatialRemainder,add_sub_cancel] at hBound
  simp only [Real.norm_eq_abs,abs_sq]
  calc
    _ ≤ ‖y-p.1‖^2/(k+1 : ℝ) := hBound
    _ = (1/(k+1 : ℝ))*‖y-p.1‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hk.le (sq_nonneg _)

theorem peano_countable_of_littleO {n : ℕ} {u : Point n → ℝ}
    {G : Point n → (Space n →L[ℝ] ℝ)} {p : Point n}
    (hRem : (fun y => u (y,p.2)-u p-G p (y-p.1)-
      (1/2 : ℝ)*autoBilinearMap n (peanoMeasurableHessian u p) (y-p.1) (y-p.1))
        =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) : p ∈ peanoCountableGoodSet u G := by
  intro k
  have hc : 0 < 1/(k+1 : ℝ) := by positivity
  obtain ⟨d,hd,hBound⟩ := Metric.eventually_nhds_iff.mp (hRem.bound hc)
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hd
  refine ⟨m,?_⟩
  intro q hq
  let v := TopologicalSpace.denseSeq (Space n) q
  have hMem : dist (p.1+v) p.1 < d := by
    simpa only [dist_eq_norm,add_sub_cancel_left] using hq.trans hm
  have hAt := hBound hMem
  simpa only [peanoSpatialRemainder,add_sub_cancel_left,Real.norm_eq_abs,
    abs_sq,div_eq_mul_inv,mul_comm,v,one_mul] using hAt

end Yau.LeafProofs.L05AutonomousAux
