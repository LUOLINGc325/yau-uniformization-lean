import Yau.Proofs.U03Polynomial
import Yau.Proofs.U03Radius
import spec.CHAIN.CONTRACTS

/-! Surjectivity of the exact open coordinate image from the original dynamics. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.U03Proof

variable {n : ℕ}

theorem image_eq_univ_of_dynamics
    {M : ComplexManifold n}
    (global : Uniformization.OpenCoordinateData n M)
    (G Ginv : ℕ → PolyMap n) (s : ℕ → ℝ) (sigma gamma hm : ℝ)
    (himage : ImageDynamics global G Ginv s sigma gamma)
    (hdegree : ForwardDegreeControl G s hm) :
    global.image = Set.univ := by
  classical
  rcases himage with ⟨hzero, htend, _hgamma, hgap, hauto, hsmall, hinv⟩
  rcases hdegree with ⟨D, hD, hgood⟩
  by_contra hproper
  obtain ⟨hAne, hAbdd, hRpos, hclosed⟩ :=
    proper_open_radius global.image global.image_open hzero hproper
  obtain ⟨R1, R2, hR1, hR1star, hstarR2, hratio⟩ :=
    radii_around hRpos hD hgap
  have hR12 : R1 < R2 := hR1star.trans hstarR2
  have hKsub := hclosed R1 hR1 hR1star
  have hKcompact : IsCompact (Metric.closedBall (0 : ComplexVector n) R1) :=
    isCompact_closedBall (0 : ComplexVector n) R1
  have hsmallK := hsmall _ hKsub hKcompact
  have hpositive : ∀ᶠ k in atTop, 0 < s k :=
    htend.eventually (eventually_gt_atTop 0)
  have hall : ∀ᶠ k in atTop,
      (∀ z ∈ Metric.closedBall (0 : ComplexVector n) R1,
        ‖(forwardComp G k).eval z‖ ≤ Real.exp (-(sigma / 2) * s k)) ∧
      (∀ w : ComplexVector n, ‖w‖ < Real.exp (-gamma * s k) →
        (backwardComp Ginv k).eval w ∈ global.image) ∧
      0 < s k := by
    filter_upwards [hsmallK, hinv, hpositive] with k hk1 hk2 hk3
    exact ⟨hk1, hk2, hk3⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  obtain ⟨j, k, _hNj, hNk, _hclock, hdeg⟩ := hgood N
  obtain ⟨hsmallk, hinvk, hsk⟩ := hN k hNk
  have hgrowth : ∀ z : ComplexVector n, ‖z‖ < R2 →
      ‖(forwardComp G k).eval z‖ < Real.exp (-gamma * s k) := by
    intro z hz
    have hbound : ∀ w : ComplexVector n, ‖w‖ ≤ R1 →
        ‖(forwardComp G k).eval w‖ ≤ Real.exp (-(sigma / 2) * s k) := by
      intro w hw
      exact hsmallk w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
    exact (polynomial_growth_closedBall (forwardComp G k)
      (forwardComp G k).degree le_rfl hR1 hR12 hbound hz.le).trans_lt
        (power_mul_exp_lt hD hsk hR1 hR12 hdeg hratio)
  have hBall : Metric.ball (0 : ComplexVector n) R2 ⊆ global.image := by
    intro z hz
    have hz' : ‖z‖ < R2 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hmem := hinvk ((forwardComp G k).eval z) (hgrowth z hz')
    change (backwardComp Ginv k).eval ((forwardComp G k).eval z) ∈
      (global.image : Set (ComplexVector n)) at hmem
    rw [inverse_eval_forward (hauto k) z] at hmem
    exact hmem
  have hR2pos : 0 < R2 := hRpos.trans hstarR2
  have hR2le : R2 ≤ centeredImageRadius global.image :=
    le_csSup hAbdd ⟨hR2pos, hBall⟩
  exact (not_lt_of_ge hR2le) hstarR2

end Yau.Blueprint.U03Proof

namespace Yau.NodeProofs

/-- The full frozen producer, uniform in all maps, clocks and dimensions. -/
theorem U03_proved : Yau.BlueprintContracts.U03_contract := by
  intro n M global G Ginv s sigma gamma hm himage hdegree
  exact ⟨⟨Blueprint.U03Proof.image_eq_univ_of_dynamics global G Ginv s
    sigma gamma hm himage hdegree, PUnit.unit⟩⟩

end Yau.NodeProofs
