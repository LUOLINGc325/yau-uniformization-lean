import Yau.LeafProofs.L17LocalizedSchauderFinite
import Yau.LeafProofs.L17LocalizedSchauderCompositionBounds

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Neighborhood finiteness, rather than finiteness at a single point, permits
the actual iterated derivative to pass through the literal finsum. -/
theorem iteratedFDeriv_finsum (f : ι → E → F) (I : Finset ι) (k : ℕ) {x : E}
    (hf : ∀ i ∈ I, ContDiffAt ℝ (k : ℕ∞ω) (f i) x)
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0) :
    iteratedFDeriv ℝ k (fun z => ∑ᶠ i, f i z) x = ∑ᶠ i, iteratedFDeriv ℝ k (f i) x := by
  classical
  rw [((finsum_eventually_eq_sum f I hzero).iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply hf]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  have heq : f i =ᶠ[𝓝 x] (fun _ => 0) := hzero.mono (fun z hz => hz i hn)
  exact hi ((heq.iteratedFDeriv ℝ k).eq_of_nhds.trans (iteratedFDeriv_zero_function k x))

theorem contDiffAt_finsum (f : ι → E → F) (I : Finset ι) (k : ℕ) {x : E}
    (hf : ∀ i ∈ I, ContDiffAt ℝ (k : ℕ∞ω) (f i) x)
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0) :
    ContDiffAt ℝ (k : ℕ∞ω) (fun z => ∑ᶠ i, f i z) x := by
  have hsum : ContDiffAt ℝ (k : ℕ∞ω) (fun z => ∑ i ∈ I, f i z) x :=
    ContDiffAt.sum hf
  exact hsum.congr_of_eventuallyEq (finsum_eventually_eq_sum f I hzero)

end Yau.LeafProofs.L17LocalizedSchauderAux
