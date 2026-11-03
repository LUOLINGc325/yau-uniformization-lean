import Yau.Proofs.P03PoleStrictifier
import Yau.Proofs.P03ManifoldPole
import Yau.Proofs.P03StrictPshCharts

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- A single global multiplier absorbs one genuine manifold cutoff pole,
with the same multiplier in all charts and at every regularization index. -/
theorem exists_manifold_pole_strictifier (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    (p : M.Carrier) (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) p)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ j : ℕ, ∀ a : M.Carrier, ∀ z ∈ chartTarget a, ∀ v,
      complexLeviQuadratic (inChart a ψ) z v ≤
        complexLeviQuadratic (inChart a (fun x => k * ψ x +
          manifoldCutoffPole c b (poleEpsilon j) x)) z v := by
  have hball : Metric.closedBall (chartPt p p) b.rOut ⊆ chartTarget p := by
    have hb := b.closedBall_subset
    simp only [ModelWithCorners.range_eq_univ, inter_univ] at hb
    convert! hb using 1
  obtain ⟨k, hk, hbound⟩ := exists_pole_strictifier (chartPt p p) b.toContDiffBump c hc
    (isOpen_extChartAt_target p) (inChart p ψ) (hψ.1 p)
    (fun z hz => strictPsh_chart_posDef hψ p hz) hball
  refine ⟨k, hk, ?_⟩
  intro j a z hz v
  let F : M.Carrier → ℝ := fun x => k * ψ x + manifoldCutoffPole c b (poleEpsilon j) x
  have hF : SmoothFn F := by
    intro a
    exact (contDiffOn_const.mul (hψ.1 a)).add
      (manifoldCutoffPole_smooth c b (poleEpsilon_pos j) a)
  by_cases hp : chartInv a z ∈ (extChartAt (ComplexModel n) p).source
  · let y := chartPt p (chartInv a z)
    have hy : y ∈ chartTarget p := (extChartAt (ComplexModel n) p).map_source hp
    have he : inChart p F =ᶠ[𝓝 y]
        (fun w => k * inChart p ψ w +
          cutoffPoleRegularization c b.toContDiffBump (chartPt p p) (poleEpsilon j) w) := by
      filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with w hw
      change k * inChart p ψ w + inChart p (manifoldCutoffPole c b (poleEpsilon j)) w = _
      rw [manifoldCutoffPole_inChart c b (poleEpsilon j) hw]
    rw [inChart_complexLevi_transition hψ.1 a p hz hp,
      inChart_complexLevi_transition hF a p hz hp,
      complexLeviQuadratic_congr_germ he]
    exact hbound j y hy _
  · have hnot : chartInv a z ∉ tsupport (manifoldCutoffPole c b (poleEpsilon j)) := by
      intro hx
      exact hp (b.tsupport_subset_extChartAt_source
        (manifoldCutoffPole_tsupport c b (poleEpsilon j) hx))
    have he0 : manifoldCutoffPole c b (poleEpsilon j) =ᶠ[𝓝 (chartInv a z)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have he : inChart a F =ᶠ[𝓝 z] (fun w => k * inChart a ψ w) := by
      filter_upwards [(continuousAt_extChartAt_symm'' hz).eventually he0] with w hw
      change k * ψ (chartInv a w) + manifoldCutoffPole c b (poleEpsilon j) (chartInv a w) = _
      change manifoldCutoffPole c b (poleEpsilon j) (chartInv a w) = 0 at hw
      rw [hw, add_zero]
      rfl
    rw [complexLeviQuadratic_congr_germ he,
      complexLeviQuadratic_const_mul
        (((hψ.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds hz)).of_le (by simp))]
    have hnonneg : 0 ≤ complexLeviQuadratic (inChart a ψ) z v :=
      (leviC_posSemidef_iff
        (((hψ.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds hz)).of_le (by simp))).mp
        (strictPsh_chart_posDef hψ a hz).posSemidef v
    exact le_mul_of_one_le_left hnonneg hk

end Yau.NodeProofs.P03Aux
