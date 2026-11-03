import Yau.LeafProofs.L05PucciHarnackExactBarrier

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_qminus_isOpen (n : ℕ) : IsOpen (harnackQminus n) :=
  Metric.isOpen_ball.prod isOpen_Ioo

theorem harnack_qminus_nonempty (n : ℕ) : (harnackQminus n).Nonempty := by
  refine ⟨((0 : Space n),(-5/8 : ℝ)),?_,?_,?_⟩
  · exact Metric.mem_ball_self (by norm_num)
  · norm_num
  · norm_num

theorem harnack_qminus_measure_ne_top (n : ℕ) : (volume : Measure (Point n)) (harnackQminus n)≠⊤ := by
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  exact ne_top_of_le_ne_top hD.measure_ne_top (measure_mono harnack_qminus_subset_unitClosed)

theorem harnack_qminus_mu_pos (n : ℕ) : 0 < harnackMu (harnackQminus n) := by
  have hPos := (harnack_qminus_isOpen n).measure_pos volume (harnack_qminus_nonempty n)
  exact ENNReal.toReal_pos (ne_of_gt hPos) (harnack_qminus_measure_ne_top n)

theorem harnack_qminus_volume (n : ℕ) :
    harnackMu (harnackQminus n)=((volume : Measure (Space n)) (Metric.ball 0 1)).toReal*
      (1/4 : ℝ)^(2*n+1) := by
  have hBall := Measure.addHaar_ball_of_pos (volume : Measure (Space n)) (0 : Space n)
    (by norm_num : (0 : ℝ) < 1/4)
  rw [complexVector_finrank_real] at hBall
  have hLen : (-1/2 : ℝ)-(-3/4)=1/4 := by norm_num
  rw [harnackMu,harnackQminus,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo,hLen,hBall,
    ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1/4 : ℝ)^(2*n)),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/4),pow_succ]
  ring

theorem harnack_sublevel_measurable {n : ℕ} {v : Point n → ℝ} {S : Set (Point n)}
    (hv : ContinuousOn v (unitClosed n)) (hS : MeasurableSet S) (hSD : S ⊆ unitClosed n) (M : ℝ) :
    MeasurableSet {z ∈ S | v z ≤ M} := by
  have hD : IsClosed (unitClosed n) := Metric.isClosed_closedBall.prod isClosed_Icc
  have hClosed := hv.preimage_isClosed_of_isClosed hD (isClosed_Iic : IsClosed (Iic M))
  have hEq : {z ∈ S | v z ≤ M}=S ∩ (unitClosed n ∩ {z | v z ≤ M}) := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1,hSD hz.1,hz.2⟩
    · intro hz
      exact ⟨hz.1,hz.2.2⟩
  rw [hEq]
  exact hS.inter hClosed.measurableSet

theorem harnack_qminus_sublevel_measurable {n : ℕ} {v : Point n → ℝ}
    (hv : ContinuousOn v (unitClosed n)) (M : ℝ) :
    MeasurableSet {z ∈ harnackQminus n | v z ≤ M} :=
  harnack_sublevel_measurable hv (harnack_qminus_isOpen n).measurableSet harnack_qminus_subset_unitClosed M

theorem harnack_mu_mono {n : ℕ} {S T : Set (Point n)}
    (hT : (volume : Measure (Point n)) T≠⊤) (hST : S ⊆ T) : harnackMu S ≤ harnackMu T :=
  ENNReal.toReal_mono hT (measure_mono hST)

end Yau.LeafProofs.L05Aux
