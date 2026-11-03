import Yau.Proofs.F03CompactHeatLocalJetRate
import Yau.Proofs.F03CompactLinearRate

/-! Genuine compact-chart C∞ initial convergence for every actual compact scalar heat evolution. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem wholeCompactHeat_compact_jet_rate
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hKc : IsCompact K) (hKt : K ⊆ chartTarget a) (m : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ t,0 < t → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun w =>
        wholeCompactHeat g hK μ hμ k (chartInv a w) t-k (chartInv a w)) z‖ ≤ C*t := by
  apply compact_linear_rate_of_local K hKc
    (fun t z => ‖iteratedFDeriv ℝ m (fun w =>
      wholeCompactHeat g hK μ hμ k (chartInv a w) t-k (chartInv a w)) z‖)
  intro z hz
  obtain ⟨r,hr,C,hC,hRate⟩ := wholeCompactHeat_local_jet_rate g hK μ hμ k a z (hKt hz) m
  refine ⟨Metric.ball z r,Metric.isOpen_ball,Metric.mem_ball_self hr,C,hC,fun t ht y _hy hyU => ?_⟩
  have hShift : y-z ∈ Metric.ball (0 : ComplexVector n) r := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hyU
  simpa only [sub_add_cancel] using hRate t ht (y-z) hShift

theorem wholeCompactHeat_compact_initial_jets
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hKc : IsCompact K) (hKt : K ⊆ chartTarget a)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ,0 < δ ∧ ∀ t,0 < t → t < δ → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun w =>
        wholeCompactHeat g hK μ hμ k (chartInv a w) t-k (chartInv a w)) z‖ < ε := by
  obtain ⟨C,hC,hRate⟩ := wholeCompactHeat_compact_jet_rate g hK μ hμ k a K hKc hKt m
  let δ := ε/(C+1)
  have hC1 : 0 < C+1 := by linarith
  have hδ : 0 < δ := div_pos hε hC1
  refine ⟨δ,hδ,fun t ht htd z hz => (hRate t ht z hz).trans_lt ?_⟩
  have h := mul_lt_mul_of_pos_right htd hC1
  have hEq : δ*(C+1)=ε := by dsimp [δ];field_simp
  rw [hEq] at h
  nlinarith

end Yau.Proofs.F03Aux
