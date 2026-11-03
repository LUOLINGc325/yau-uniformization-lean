import Yau.LeafProofs.L17AtlasPacking

/-! A genuine countable uniform cover with a locally uniform overlap budget. -/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

def coverScale {g : HermitianField M} (A : BoundedChartFamily g) : ℝ :=
  Real.sqrt (2 * (A.bound 0)⁻¹) / 8

def overlapScale {g : HermitianField M} (A : BoundedChartFamily g) : ℝ :=
  coverScale A + Real.sqrt (2 * A.bound 0)

theorem coverScale_pos {g : HermitianField M} (A : BoundedChartFamily g) :
    0 < coverScale A := by
  have hC := A.bound_pos 0
  unfold coverScale
  positivity

theorem overlapScale_pos {g : HermitianField M} (A : BoundedChartFamily g) :
    0 < overlapScale A := add_pos_of_pos_of_nonneg (coverScale_pos A) (Real.sqrt_nonneg _)

theorem BoundedChartFamily.exists_uniform_net_cover
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < A.radius →
      overlapScale A * ρ < Real.sqrt (2 * (A.bound 0)⁻¹) * (A.radius / 2) →
      ∃ S : Set M.Carrier, S.Countable ∧
        S.Pairwise (fun p q => coverScale A * ρ ≤ inducedDistance g p q) ∧
        (∀ x : M.Carrier, ∃ p ∈ S, x ∈ A.chart p '' ball 0 (ρ / 4)) ∧
        ∀ x : M.Carrier, ∃ V ∈ 𝓝 x,
          {p : S | ((A.chart p '' closedBall 0 ρ) ∩ V).Nonempty}.Finite ∧
          Nat.card {p : S | ((A.chart p '' closedBall 0 ρ) ∩ V).Nonempty} ≤ N := by
  obtain ⟨N, hN⟩ := A.exists_local_net_bound hg (overlapScale A) (coverScale A)
    (overlapScale_pos A) (coverScale_pos A)
  refine ⟨N, ?_⟩
  intro ρ hρ hρr hbudget
  have hs : 0 < coverScale A * ρ := mul_pos (coverScale_pos A) hρ
  obtain ⟨S, hcount, hsep, hcover⟩ := exists_intrinsic_countable_net g hg hs
  refine ⟨S, hcount, hsep, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, hxp⟩ := hcover x
    refine ⟨p, hp, A.chartBall_contains_distance_ball hg p x
      (by positivity) (by linarith) ?_⟩
    rw [L23Aux.inducedDistance_symm g hg]
    have hc := coverScale_pos A
    have hscale : coverScale A * ρ < Real.sqrt (2 * (A.bound 0)⁻¹) * (ρ / 4) := by
      unfold coverScale at *
      nlinarith
    exact hxp.trans hscale
  · intro x
    let := L23Aux.metricSpaceOfField g hg
    let V := ball x (coverScale A * ρ)
    let I := {p : S | ((A.chart p '' closedBall 0 ρ) ∩ V).Nonempty}
    have hnear (p : I) : inducedDistance g x (p.1 : M.Carrier) ≤ overlapScale A * ρ := by
      obtain ⟨y, ⟨z, hz, hzy⟩, hyV⟩ := p.2
      have hzbg : z ∈ ball 0 A.radius := (mem_closedBall.mp hz).trans_lt hρr
      have hd := A.distance_le hg (p.1 : M.Carrier)
        (mem_ball_self A.radius_pos) hzbg
      rw [A.center (p.1 : M.Carrier), hzy] at hd
      have hzdist : dist (0 : ComplexVector n) z ≤ ρ := by
        simpa only [dist_comm] using mem_closedBall.mp hz
      have hdy : inducedDistance g y (p.1 : M.Carrier) ≤ Real.sqrt (2 * A.bound 0) * ρ := by
        rw [L23Aux.inducedDistance_symm g hg]
        exact hd.trans (mul_le_mul_of_nonneg_left hzdist (Real.sqrt_nonneg _))
      have hxy : inducedDistance g x y < coverScale A * ρ := by
        simpa only [V, mem_ball, dist_comm, L23Aux.metricSpaceOfField_dist] using hyV
      calc
        inducedDistance g x (p.1 : M.Carrier) ≤ inducedDistance g x y +
          inducedDistance g y (p.1 : M.Carrier) := L23Aux.inducedDistance_triangle g hg x y _
        _ ≤ coverScale A * ρ + Real.sqrt (2 * A.bound 0) * ρ := add_le_add hxy.le hdy
        _ = overlapScale A * ρ := by unfold overlapScale; ring
    have hsepi : Pairwise (fun p q : I => coverScale A * ρ ≤
        inducedDistance g (p.1 : M.Carrier) (q.1 : M.Carrier)) := by
      intro p q hpq
      apply hsep p.1.2 q.1.2
      intro heq
      apply hpq
      apply Subtype.ext
      exact Subtype.ext heq
    obtain ⟨hfinite, hcard⟩ := hN ρ hρ hbudget x I (fun p => (p.1 : M.Carrier)) hnear hsepi
    let := hfinite
    exact ⟨V, ball_mem_nhds x hs, Set.toFinite I, hcard⟩

end Yau.LeafProofs.L17Aux
