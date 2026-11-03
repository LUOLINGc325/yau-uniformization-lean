import Yau.LeafProofs.L17AtlasNets

/-! Uniform local overlap budgets from the original chart distance comparisons. -/

noncomputable section

open Set Metric
open scoped Topology

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The overlap budget is independent of the center, radius, and index family. -/
theorem BoundedChartFamily.exists_local_net_bound
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (L σ : ℝ) (_hL : 0 < L) (hσ : 0 < σ) :
    ∃ N : ℕ, ∀ ρ : ℝ, 0 < ρ →
      L * ρ < Real.sqrt (2 * (A.bound 0)⁻¹) * (A.radius / 2) →
      ∀ (x : M.Carrier) (ι : Type*) (f : ι → M.Carrier),
        (∀ i, inducedDistance g x (f i) ≤ L * ρ) →
        Pairwise (fun i j => σ * ρ ≤ inducedDistance g (f i) (f j)) →
          Finite ι ∧ Nat.card ι ≤ N := by
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  let b := Real.sqrt (2 * A.bound 0)
  have hC := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hδ : 0 < σ / b := div_pos hσ hb
  obtain ⟨N, hN⟩ := exists_uniform_scaled_packing_bound n (c⁻¹ * L) (σ / b) hδ
  refine ⟨N, ?_⟩
  intro ρ hρ hbudget x ι f hnear hsep
  have hr : 0 < A.radius / 2 := by have := A.radius_pos; positivity
  have hrr : A.radius / 2 < A.radius := by have := A.radius_pos; linarith
  have hsmall (i : ι) : inducedDistance g x (f i) < c * (A.radius / 2) :=
    (hnear i).trans_lt hbudget
  have himage (i : ι) : f i ∈ A.chart x '' ball 0 (A.radius / 2) :=
    A.chartBall_contains_distance_ball hg x (f i) hr hrr (hsmall i)
  have hsource (z : ComplexVector n) (hz : z ∈ ball 0 (A.radius / 2)) :
      z ∈ (A.chart x).source := A.closedBall_source x
    (mem_closedBall.mpr ((mem_ball.mp hz).le.trans hrr.le))
  have htarget (i : ι) : f i ∈ (A.chart x).target := by
    obtain ⟨z, hz, heq⟩ := himage i
    rw [← heq]
    exact (A.chart x).map_source (hsource z hz)
  have hcoord (i : ι) : (A.chart x).symm (f i) ∈ ball 0 A.radius := by
    obtain ⟨z, hz, heq⟩ := himage i
    have hinv : (A.chart x).symm (f i) = z := by
      rw [← heq]
      exact (A.chart x).left_inv (hsource z hz)
    rw [hinv]
    exact (mem_ball.mp hz).trans hrr
  have heq (i : ι) : A.chart x ((A.chart x).symm (f i)) = f i :=
    (A.chart x).right_inv (htarget i)
  apply hN ρ hρ ι (fun i => (A.chart x).symm (f i))
  · intro i
    calc
      ‖(A.chart x).symm (f i)‖ ≤ c⁻¹ * inducedDistance g x (f i) :=
        A.coordinate_norm_le_distance hg x (f i) hr hrr (hsmall i)
      _ ≤ c⁻¹ * (L * ρ) := mul_le_mul_of_nonneg_left (hnear i) (inv_nonneg.mpr hc.le)
      _ = (c⁻¹ * L) * ρ := by ring
  · intro i j hij
    have hu := A.distance_le hg x (hcoord i) (hcoord j)
    rw [heq i, heq j] at hu
    have hh : σ * ρ ≤ b * dist ((A.chart x).symm (f i)) ((A.chart x).symm (f j)) :=
      (hsep hij).trans hu
    have hdiv : (σ * ρ) / b ≤ dist ((A.chart x).symm (f i)) ((A.chart x).symm (f j)) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hh)
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

end Yau.LeafProofs.L17Aux
