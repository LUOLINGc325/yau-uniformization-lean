import Yau.LeafProofs.L05AutonomousOscillationDecayEnergy

noncomputable section
open Set
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The stated 9/16 and 5/8 collars really buffer the full 1/64 backward parent cylinder. -/
theorem auto_jet_pair_parent_buffer {n : ℕ} {p q : Point n}
    (hp : p ∈ autoClosed (0 : Space n) (9/16) 0)
    (hq : q ∈ autoClosed (0 : Space n) (9/16) 0) :
    autoClosed p.1 (1/64) (max p.2 q.2) ⊆ autoClosed (0 : Space n) (5/8) 0 := by
  have hpx : ‖p.1‖ ≤ 9/16 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1
  have hpt : (0 : ℝ)-(9/16)^2 ≤ p.2 ∧ p.2 ≤ 0 := hp.2
  have hqt : (0 : ℝ)-(9/16)^2 ≤ q.2 ∧ q.2 ≤ 0 := hq.2
  have htop : max p.2 q.2 ≤ 0 := max_le hpt.2 hqt.2
  intro z hz
  constructor
  · change dist z.1 0 ≤ 5/8
    rw [dist_zero_right]
    have hdist : ‖z.1-p.1‖ ≤ 1/64 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz.1
    have hn := norm_add_le (z.1-p.1) p.1
    rw [sub_add_cancel] at hn
    linarith only [hn,hdist,hpx]
  · have hzt : max p.2 q.2-(1/64 : ℝ)^2 ≤ z.2 ∧ z.2 ≤ max p.2 q.2 := hz.2
    change (0 : ℝ)-(5/8)^2 ≤ z.2 ∧ z.2 ≤ 0
    constructor
    · have hmax := le_max_left p.2 q.2
      linarith only [hzt.1,hpt.1,hmax]
    · exact hzt.2.trans htop

/-- The actual common terminal time of two good points stays strictly below zero. -/
theorem auto_jet_good_pair_top_neg {n : ℕ} {S : Set (Point n)}
    (hS : S ⊆ autoOpen (0 : Space n) (5/8) 0) {p q : Point n}
    (hp : p ∈ S) (hq : q ∈ S) : max p.2 q.2 < 0 :=
  max_lt (hS hp).2.2 (hS hq).2.2

end Yau.LeafProofs.L05AutonomousAux
