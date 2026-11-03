import Yau.LeafProofs.L17BackgroundFunctionSmooth

/-! A locally finite derivative estimate uses the actual local overlap count. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

theorem norm_iteratedFDeriv_finsum_le
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ι → E → F} {x : E} {k : ℕ} (I : Finset ι) (B : ℝ)
    (hf : ∀ i ∈ I, ContDiffAt ℝ k (f i) x)
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0)
    (hbound : ∀ i ∈ I, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun z => ∑ᶠ i, f i z) x‖ ≤ (I.card : ℝ) * B := by
  classical
  have heq : (fun z => ∑ᶠ i, f i z) =ᶠ[𝓝 x] (fun z => ∑ i ∈ I, f i z) := by
    filter_upwards [hzero] with z hz
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hnot
    exact hi (hz i hnot)
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_sum_apply hf]
  calc
    _ ≤ ∑ i ∈ I, ‖iteratedFDeriv ℝ k (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum hbound
    _ = (I.card : ℝ) * B := by simp

end Yau.LeafProofs.L17Aux
