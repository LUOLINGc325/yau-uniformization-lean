import Yau.Proofs.V04FactorFourierBridge
import Yau.Proofs.D05ClosedFactors
import Yau.Proofs.D06OriginalBoundaryBridge

/-! The actual D06 source factors have the sharp original Fourier bound
and the inverse norm bound on the entire closed disc. The factors and
normalization are unchanged in every identity. -/

open MeasureTheory AddCircle
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem matrixDSq_circle_eq_factorCircleDirichlet
    (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ) :
    matrixDSq (fun θ : ℝ => A (θ : HardyCircle)) = factorCircleDirichlet A := by
  let u := fun (θ : ℝ) (p : Fin r × Fin r) => A (θ : HardyCircle) p.1 p.2
  have hp (p : Fin r × Fin r) : Function.Periodic (fun θ => u θ p) (2 * Real.pi) := by
    intro θ
    simp only [u, AddCircle.coe_add_period]
  change boundaryDSq u = _
  rw [boundaryDSq_eq_sum_periodic_lift u hp]
  change (∑ p : Fin r × Fin r, circleDirichlet (hp p).lift) = _
  simp only [factorCircleDirichlet, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have heq : (hp (i, j)).lift = fun t : HardyCircle => A t i j := by
    funext t
    induction t using Quotient.inductionOn' with
    | h θ => rfl
  rw [heq]

theorem boundarySource_inverse_matrixDSq (s : BoundarySource r) :
    matrixDSq (onCircle s.Hinv) ≤ ENNReal.ofReal (1 / (2 * s.m ^ 3)) * matrixDSq s.L := by
  have hc := s.closed_complex_smooth
  have hm := s.m_pos
  have hP : ContinuousOn s.Hinv (Metric.closedBall 0 1) :=
    continuousOn_pi.2 (fun i => continuousOn_pi.2 (fun j => (hc i j).2.continuousOn))
  have hd (θ : HardyCircle) : circleDifference s.Pcircle θ ≤
      1 / (2 * s.m ^ 3) * circleDifference s.symbol θ := by
    rw [circleDifference_congr_ae _ _ s.Pcircle_trace_ae]
    exact hardyPTrace_difference_sharp s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower
      s.M s.M_nonneg s.upper θ
  have hh := factorCircleDirichlet_le_of_difference_bound s.Pcircle s.symbol
    (s.Pcircle_continuous hP) s.symbol_continuous (by positivity : 0 ≤ 1 / (2 * s.m ^ 3)) hd
  have heqP : matrixDSq (onCircle s.Hinv) = factorCircleDirichlet s.Pcircle := by
    rw [← matrixDSq_circle_eq_factorCircleDirichlet]
    congr 1
    funext θ
    exact (s.Pcircle_coe θ).symm
  have heqL : matrixDSq s.L = factorCircleDirichlet s.symbol := by
    rw [← matrixDSq_circle_eq_factorCircleDirichlet]
    congr 1
  rw [heqP, heqL]
  exact hh

theorem boundarySource_inverse_closed_bound (s : BoundarySource r) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, matOpNormR (s.Hinv z) ≤ (Real.sqrt s.m)⁻¹ := by
  have hc := s.closed_complex_smooth
  have hP : ContinuousOn s.Hinv (Metric.closedBall 0 1) :=
    continuousOn_pi.2 (fun i => continuousOn_pi.2 (fun j => (hc i j).2.continuousOn))
  have hn : ContinuousOn (fun z => matOpNormR (s.Hinv z)) (Metric.closedBall 0 1) := hP.norm
  have hclosure : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall (0 : ℂ) 1 :=
    closure_ball _ one_ne_zero
  rw [← hclosure] at hn ⊢
  exact le_on_closure (fun z hz => (s.interior_bounds z hz).2) hn continuousOn_const

end Yau.Blueprint.V04Proof
