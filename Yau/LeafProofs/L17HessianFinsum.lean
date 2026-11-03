import Yau.LeafProofs.L17LocalizedSchauderSumJets

open Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

theorem secondFDeriv_finsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ι → E → F) (I : Finset ι) {x : E}
    (hf : ∀ i ∈ I, ContDiffAt ℝ 2 (f i) x)
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0) :
    fderiv ℝ (fderiv ℝ (fun z => ∑ᶠ i, f i z)) x =
      ∑ᶠ i, fderiv ℝ (fderiv ℝ (f i)) x := by
  classical
  have hnear : ∀ᶠ z in 𝓝 x, ∀ i ∈ I, DifferentiableAt ℝ (f i) z := by
    apply (eventually_all_finset I).mpr
    intro i hi
    have h := (hf i hi).eventually (by norm_num)
    exact h.mono (fun z hz => hz.differentiableAt (by norm_num))
  have hFinite : fderiv ℝ (fun z => ∑ i ∈ I, f i z) =ᶠ[𝓝 x]
      (fun z => ∑ i ∈ I, fderiv ℝ (f i) z) := by
    filter_upwards [hnear] with z hz
    exact fderiv_fun_sum hz
  have hEqual := (L17LocalizedSchauderAux.finsum_eventually_eq_sum f I hzero).fderiv (𝕜 := ℝ)
  have hSecond := (hEqual.trans hFinite).fderiv_eq (𝕜 := ℝ)
  rw [hSecond,fderiv_fun_sum (fun i hi =>
    ((hf i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  have hEq : f i =ᶠ[𝓝 x] (fun _ => 0) := hzero.mono (fun z hz => hz i hn)
  have hD2 : fderiv ℝ (fderiv ℝ (f i)) x = 0 := by
    simpa using ((hEq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ))
  exact hi hD2

end Yau.LeafProofs.L17Aux
