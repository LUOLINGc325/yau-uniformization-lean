import Yau.Proofs.C01PathEnergy

/-! Every prefix of a genuine constant-speed unit path has distance
at most its full speed, without any completeness assumption. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem actualPathELength_eq_of_constant_speedSq
    (k : HermitianField M) (γ : ℝ → M.Carrier) (d : ℝ) (hd : 0 ≤ d)
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      realTangentSpeedSq k (γ u) (realCurveVelocity γ u) = d ^ 2) :
    actualPathELength k γ 0 1 = ENNReal.ofReal d := by
  rw [actualPathELength_eq_lintegral]
  have heq : (fun u => ENNReal.ofReal (actualPathSpeed k γ u)) =ᵐ[
      volume.restrict (Set.Icc (0 : ℝ) 1)] (fun _ => ENNReal.ofReal d) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have H := actualPathSpeed_sq k γ u
    rw [hspeed u hu] at H
    have hnonneg : 0 ≤ actualPathSpeed k γ u := Real.sqrt_nonneg _
    have he : actualPathSpeed k γ u = d := by nlinarith only [H, hnonneg, hd]
    rw [he]
  rw [lintegral_congr_ae heq]
  simp

theorem constant_speed_path_distance_le
    (k : HermitianField M) (hk : MetricSmooth k) (γ : ℝ → M.Carrier)
    (d : ℝ) (hd : 0 ≤ d)
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      realTangentSpeedSq k (γ u) (realCurveVelocity γ u) = d ^ 2) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ →
    ∀ u ∈ Set.Icc (0 : ℝ) 1, inducedDistance k (γ 0) (γ u) ≤ d := by
  letI := manifold_realSmooth M
  intro hγ u hu
  have H := (distance_le_smooth_segment_length k hk γ hγ 0 u hu.1).trans
    (actualPathELength_mono k γ le_rfl hu.2)
  rw [actualPathELength_eq_of_constant_speedSq k γ d hd hspeed] at H
  exact (ENNReal.ofReal_le_ofReal_iff hd).mp H

end Yau.NodeProofs.C01Aux
