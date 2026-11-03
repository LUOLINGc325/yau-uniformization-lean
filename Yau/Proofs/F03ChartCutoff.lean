import Yau.LeafProofs.L18

/-! A genuine compact smooth cutoff in a prescribed interior chart ball. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem chartPushforwardZero_tsupport (a : M.Carrier)
    {φ : ComplexVector n → ℝ} (hc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ chartTarget a) :
    tsupport (chartPushforwardZero a φ) ⊆ chartInv a '' tsupport φ := by
  have hK : IsCompact (chartInv a '' tsupport φ) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono ht)
  apply closure_minimal _ hK.isClosed
  intro y hy
  by_cases hs : y ∈ (extChartAt (ComplexModel n) a).source
  · have hn : φ (chartPt a y) ≠ 0 := by
      simpa only [Function.mem_support,chartPushforwardZero,if_pos hs] using hy
    exact ⟨chartPt a y,subset_closure hn,(extChartAt (ComplexModel n) a).left_inv hs⟩
  · exact False.elim (hy (by simp only [chartPushforwardZero,if_neg hs]))

theorem exists_compact_chart_cutoff (a : M.Carrier) (z₀ : ComplexVector n)
    {δ : ℝ} (hδ : 0 < δ) (ht : Metric.closedBall z₀ δ ⊆ chartTarget a) :
    ∃ χ : M.Carrier → ℝ, SmoothFn χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ chartInv a '' Metric.closedBall z₀ δ ∧
      ∀ z ∈ Metric.closedBall z₀ (δ/2), χ (chartInv a z)=1 := by
  let b : ContDiffBump z₀ := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  have hb : tsupport (b : ComplexVector n → ℝ) ⊆ chartTarget a := by
    rw [b.tsupport_eq]
    exact ht
  refine ⟨chartPushforwardZero a (b : ComplexVector n → ℝ),
    smoothFn_chartPushforwardZero a b.contDiff b.hasCompactSupport hb,
    (chartPushforwardZero_properties a b.contDiff b.hasCompactSupport hb).1,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ (extChartAt (ComplexModel n) a).source
    · simp only [chartPushforwardZero,if_pos hx]
      exact ⟨b.nonneg,b.le_one⟩
    · simp only [chartPushforwardZero,if_neg hx]
      exact ⟨le_rfl,zero_le_one⟩
  · simpa only [b.tsupport_eq] using chartPushforwardZero_tsupport a b.hasCompactSupport hb
  · intro z hz
    have hzt : z ∈ chartTarget a := ht (Metric.closedBall_subset_closedBall (by linarith only [hδ]) hz)
    rw [chartPushforwardZero_chartInv a (b : ComplexVector n → ℝ) hzt]
    exact b.one_of_mem_closedBall hz

end Yau.Proofs.F03Aux
