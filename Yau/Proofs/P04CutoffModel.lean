import Yau.Proofs.P04CanonicalRegularity

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_pole_cutoff (p : M.Carrier) :
    ∃ ρ : ℝ, 0 < ρ ∧ 5*ρ^2 < 1 ∧
      Metric.closedBall (chartPt p p) (2*ρ) ⊆ chartTarget p ∧
      ∃ χ : ComplexVector n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ Metric.closedBall (chartPt p p) (3*ρ/2) ∧
        (∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1) ∧
        (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) p).mem_nhds (mem_extChartAt_target p))
  let ρ := min (δ/4) (1/4 : ℝ)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρδ : ρ ≤ δ/4 := min_le_left _ _
  have hρ1 : ρ ≤ (1/4 : ℝ) := min_le_right _ _
  have hsquare : 5*ρ^2 < 1 := by nlinarith
  have htarget : Metric.closedBall (chartPt p p) (2*ρ) ⊆ chartTarget p := by
    intro z hz
    apply hball
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith))
  let b : ContDiffBump (chartPt p p) :=
    { rIn := ρ
      rOut := 3*ρ/2
      rIn_pos := hρ
      rIn_lt_rOut := by linarith }
  refine ⟨ρ,hρ,hsquare,htarget,b,b.contDiff,b.hasCompactSupport,?_,?_,?_⟩
  · exact b.tsupport_eq.subset
  · exact fun z hz => b.one_of_mem_closedBall hz
  · exact fun z => ⟨b.nonneg,b.le_one⟩

/-- Every selected pole cutoff really has its support buffered inside its chart. -/
theorem pole_cutoff_support_in_chart (p : M.Carrier) {ρ : ℝ} (hρ : 0 < ρ)
    (htarget : Metric.closedBall (chartPt p p) (2*ρ) ⊆ chartTarget p)
    {χ : ComplexVector n → ℝ}
    (hχ : tsupport χ ⊆ Metric.closedBall (chartPt p p) (3*ρ/2)) :
    tsupport χ ⊆ chartTarget p := by
  apply hχ.trans
  apply (Metric.closedBall_subset_closedBall (by linarith : 3*ρ/2 ≤ 2*ρ)).trans htarget

end Yau.Proofs.P04Aux
