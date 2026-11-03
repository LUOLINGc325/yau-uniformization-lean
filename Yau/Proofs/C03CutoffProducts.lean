import Mathlib

/-! A cutoff supported inside the region of smoothness gives a genuinely
global smooth product, including across the boundary of that region. -/

open Set Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux

theorem contDiff_cutoff_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℝ) (f : E → ℂ) (U : Set E) (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x => (χ x : ℂ) * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hχ.contDiffAt).mul
      (hf.contDiffAt (hU.mem_nhds hx))
  · have hxt : x ∉ tsupport χ := fun h => hx (hs h)
    have hn : (tsupport χ)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hxt
    have he : (fun y => (χ y : ℂ) * f y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hn] with y hy
      have hχy : χ y = 0 := by
        by_contra hne
        exact hy (subset_closure hne)
      simp only [hχy, Complex.ofReal_zero, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

end Yau.Proofs.C03Aux
