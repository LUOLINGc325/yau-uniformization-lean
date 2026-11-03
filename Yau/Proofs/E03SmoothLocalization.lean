import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! SOURCE-ONLY E03 candidate. Input is smoothness ON an open set, not a pointwise C∞ germ. -/

noncomputable section
open scoped Topology ContDiff
open Filter Set Metric

namespace Yau.NodeProofs.E03Aux

theorem exists_global_contDiff_equal_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {O : Set E} (hO : IsOpen O) {p : E} (hp : p ∈ O) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F O) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 p] F := by
  obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp hO p hp
  let β : ContDiffBump p := ⟨R / 4, R / 2, by positivity, by linarith⟩
  have hβO : tsupport (β : E → ℝ) ⊆ O := by
    rw [β.tsupport_eq]
    intro y hy
    apply hRO
    rw [Metric.mem_ball]
    have hy' : dist y p ≤ R / 2 := hy
    linarith
  let g : E → ℝ := fun y => β y * F y
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ O
    · exact β.contDiff.contDiffAt.mul (hF.contDiffAt (hO.mem_nhds hy))
    · have hyβ : y ∉ tsupport (β : E → ℝ) := fun h => hy (hβO h)
      have hclosed : IsClosed (tsupport (β : E → ℝ)) := isClosed_closure
      have hnear : ∀ᶠ z in 𝓝 y, z ∉ tsupport (β : E → ℝ) :=
        hclosed.isOpen_compl.mem_nhds hyβ
      have heq : g =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hnear] with z hz
        have hz0 : β z = 0 := by
          by_contra hne
          exact hz (subset_closure hne)
        simp only [g, hz0, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨g, hg, ?_⟩
  filter_upwards [β.eventuallyEq_one] with y hy
  simp only [g, hy, Pi.one_apply, one_mul]

end Yau.NodeProofs.E03Aux
