import Yau.LeafProofs.L05AutonomousSpatialPeanoAE
import Yau.LeafProofs.L05AutonomousPeanoMeasurable
import Yau.LeafProofs.L05AutonomousPeanoEquation
import Yau.LeafProofs.L05AutonomousSecondBounds

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem auto_measurableJet_open_closed_subset {n : ℕ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : r ≤ R) :
    autoOpen (0 : Space n) r 0 ⊆ autoClosed 0 R 0 := by
  intro p hp
  apply autoClosed_subset 0 hr hR 0
  exact ⟨Metric.ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2.le⟩

theorem auto_measurableJet_open_unitClosed {n : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    autoOpen (0 : Space n) r 0 ⊆ unitClosed n := by
  intro p hp
  have hU := autoOpen_subset_unitOpen hr hr1 hp
  exact ⟨Metric.ball_subset_closedBall hU.1,hU.2.1.le,hU.2.2.le⟩

theorem auto_measurableJet_second_transport {n : ℕ} {u w : Point n → ℝ}
    (hwu : EqOn w u (unitClosed n)) {M : ℝ}
    (hSecond : ∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h ≠ 0 → |h| < 1/512 →
      ∀ p ∈ autoClosed (0 : Space n) (11/16) 0, |autoSecond u e h p| ≤ M) :
    ∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h ≠ 0 → |h| < 1/512 →
      ∀ p ∈ autoClosed (0 : Space n) (11/16) 0, |autoSecond w e h p| ≤ M := by
  intro e he h hh hs p hp
  obtain ⟨hp0,hpPlus,hpMinus⟩ := auto_second_closed_unit
    (by norm_num : (0 : ℝ) < 11/16) (by linarith only [hs] : (11/16 : ℝ)+|h| < 1) he.le hp
  rw [auto_second_congr hwu e h p hp0 hpPlus hpMinus]
  exact hSecond e he h hh hs p hp

theorem auto_measurableJet_holder_mono {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    {delta B C : ℝ} {Q : Set (Point n)} {f : Point n → W}
    (hf : HolderBound delta Q f B) (hBC : B ≤ C) : HolderBound delta Q f C := by
  refine ⟨hf.1.trans hBC,fun p hp => (hf.2.1 p hp).trans hBC,?_⟩
  intro p hp q hq
  exact (hf.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hBC (by
    unfold holderWeight
    positivity))

theorem auto_measurableJet_sym_bilinear {n : ℕ} (H : Sym n) :
    sym (fun i j : Yau.RIdx n => autoBilinearMap n H (Yau.realVec i) (Yau.realVec j))=H := by
  have hEntries : (fun i j : Yau.RIdx n => autoBilinearMap n H (Yau.realVec i) (Yau.realVec j))=
      (H : Mat n) := by
    ext i j
    exact autoBilinearMap_realVec H i j
  rw [hEntries]
  exact H.property.selfAdjointPart_apply ℝ

end Yau.LeafProofs.L05AutonomousAux
