import Yau.Proofs.C03SourceQuadratic

/-! Positive actual speed and preservation of the actual metric quadratic
force both vectors in the bisectional-curvature contraction to be nonzero. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem source_velocity_ne_zero_of_speed (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (γ : ℝ → ComplexVector n) (t ρ : ℝ) (hρ : 0 < ρ)
    (hγ : ContDiffAt ℝ 1 γ t) (hspeed : actualSpeedSq k γ t = ρ ^ 2) :
    deriv γ t ≠ 0 := by
  intro hzero
  rw [actualSpeedSq_source_chart hn k γ t hγ, hzero] at hspeed
  simp only [map_zero, zero_apply] at hspeed
  nlinarith [sq_pos_of_pos hρ]

theorem source_parallel_vector_ne_zero (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (z y V W : ComplexVector n) (hV : V ≠ 0)
    (hnorm : realMetricInChart k (0 : ComplexVector n) y W W =
      realMetricInChart k (0 : ComplexVector n) z V V) : W ≠ 0 := by
  intro hzero
  have hsrc : z ∈ (chartAt (ComplexVector n) (0 : ComplexVector n)).source := by
    rw [euclidean_chartSource hn]
    trivial
  have hiff : realMetricInChart k (0 : ComplexVector n) z V V = 0 ↔ V = 0 := by
    simpa only [euclidean_chartPt] using
      realMetricInChart_quadratic_eq_zero_iff k (0 : ComplexVector n) z hsrc V
  simp only [hzero, map_zero, zero_apply] at hnorm
  exact hV (hiff.mp hnorm.symm)

end Yau.Proofs.C03Aux
