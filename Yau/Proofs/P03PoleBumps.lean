import Yau.Proofs.P03ManifoldPole

open scoped Manifold Topology ContDiff
open Filter Set Metric

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- A controlled original-chart bump fits inside any prescribed manifold
neighbourhood and has outer coordinate radius at most one half. -/
theorem exists_small_pole_bump (a : M.Carrier) {U : Set M.Carrier} (hU : U ∈ 𝓝 a) :
    ∃ b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a,
      b.rOut ≤ 1 / 2 ∧ tsupport (b : M.Carrier → ℝ) ⊆ U := by
  have hi : Tendsto (chartInv a) (𝓝 (chartPt a a)) (𝓝 a) := by
    change Tendsto (extChartAt (ComplexModel n) a).symm
      (𝓝 ((extChartAt (ComplexModel n) a) a)) (𝓝 a)
    simpa only [extChartAt_to_inv] using
      (continuousAt_extChartAt_symm (I := ComplexModel n) a).tendsto
  have ht : chartTarget a ∩ chartInv a ⁻¹' U ∈ 𝓝 (chartPt a a) :=
    inter_mem ((isOpen_extChartAt_target a).mem_nhds (mem_extChartAt_target a))
      (hi.eventually hU)
  obtain ⟨R, hR, hRt⟩ := Metric.mem_nhds_iff.mp ht
  let t := min R 1
  have htpos : 0 < t := lt_min hR (by norm_num)
  have htR : t ≤ R := min_le_left _ _
  have ht1 : t ≤ 1 := min_le_right _ _
  have hball {z : ComplexVector n} (hz : z ∈ closedBall (chartPt a a) (t / 2)) :
      z ∈ ball (chartPt a a) R := by
    apply mem_ball.mpr
    have hd := mem_closedBall.mp hz
    linarith
  let b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a :=
    { rIn := t / 4
      rOut := t / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith
      closedBall_subset := by
        intro z hz
        exact (hRt (hball hz.1)).1 }
  refine ⟨b, ?_, ?_⟩
  · change t / 2 ≤ 1 / 2
    linarith
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := b.tsupport_subset_symm_image_closedBall hx
    exact (hRt (hball hz.1)).2

end Yau.NodeProofs.P03Aux
