import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Finprod

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux

theorem finsum_eventually_eq_sum {ι X F : Type*} [TopologicalSpace X] [AddCommMonoid F]
    (f : ι → X → F) (I : Finset ι) {x : X}
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0) :
    (fun z => ∑ᶠ i, f i z) =ᶠ[𝓝 x] (fun z => ∑ i ∈ I, f i z) := by
  classical
  filter_upwards [hzero] with z hz
  exact finsum_eq_sum_of_support_subset (fun i => f i z) (fun i hi => by
    by_contra hn
    exact hi (hz i hn))

theorem continuousAt_finsum {ι X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : ι → X → F) (I : Finset ι) {x : X}
    (hf : ∀ i ∈ I, ContinuousAt (f i) x)
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0) :
    ContinuousAt (fun z => ∑ᶠ i, f i z) x := by
  have hs : ContinuousAt (fun z => ∑ i ∈ I, f i z) x := tendsto_finsetSum I hf
  exact hs.congr (finsum_eventually_eq_sum f I hzero).symm

theorem norm_finsum_le {ι F : Type*} [NormedAddCommGroup F]
    (f : ι → F) (I : Finset ι) (B : ℝ)
    (hzero : ∀ i, i ∉ I → f i = 0) (hB : ∀ i ∈ I, ‖f i‖ ≤ B) :
    ‖∑ᶠ i, f i‖ ≤ (I.card : ℝ)*B := by
  classical
  rw [finsum_eq_sum_of_support_subset f (fun i hi => by
    by_contra hn
    exact hi (hzero i hn))]
  calc
    _ ≤ ∑ i ∈ I, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum hB
    _ = _ := by simp

/-- Only the endpoint active sets enter a two-point bound. -/
theorem norm_finsum_sub_le {ι F : Type*} [DecidableEq ι] [NormedAddCommGroup F]
    (f g : ι → F) (I J : Finset ι) (B : ℝ) (hB0 : 0 ≤ B)
    (hf : ∀ i, i ∉ I → f i = 0) (hg : ∀ i, i ∉ J → g i = 0)
    (hB : ∀ i ∈ I ∪ J, ‖f i-g i‖ ≤ B) :
    ‖(∑ᶠ i, f i)-(∑ᶠ i, g i)‖ ≤ ((I.card+J.card : ℕ) : ℝ)*B := by
  classical
  have hF : (∑ᶠ i, f i) = ∑ i ∈ I ∪ J, f i :=
    finsum_eq_sum_of_support_subset f (fun i hi => by
      by_contra hn
      exact hi (hf i (fun h => hn (Finset.mem_union_left J h))))
  have hG : (∑ᶠ i, g i) = ∑ i ∈ I ∪ J, g i :=
    finsum_eq_sum_of_support_subset g (fun i hi => by
      by_contra hn
      exact hi (hg i (fun h => hn (Finset.mem_union_right I h))))
  rw [hF,hG,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ I ∪ J, ‖f i-g i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ I ∪ J, B := Finset.sum_le_sum hB
    _ = ((I ∪ J).card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_union_le I J) hB0

theorem norm_finsum_sub_le_two_overlap {ι F : Type*} [DecidableEq ι] [NormedAddCommGroup F]
    (f g : ι → F) (I J : Finset ι) (N : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hI : I.card ≤ N) (hJ : J.card ≤ N)
    (hf : ∀ i, i ∉ I → f i = 0) (hg : ∀ i, i ∉ J → g i = 0)
    (hB : ∀ i ∈ I ∪ J, ‖f i-g i‖ ≤ B) :
    ‖(∑ᶠ i, f i)-(∑ᶠ i, g i)‖ ≤ (2*(N : ℝ))*B := by
  apply (norm_finsum_sub_le f g I J B hB0 hf hg hB).trans
  apply mul_le_mul_of_nonneg_right _ hB0
  norm_cast
  omega

theorem norm_smul_finsum_sub_le_two_overlap {ι F : Type*} [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : ι → F) (I J : Finset ι) (N : ℕ) (c B : ℝ) (hB0 : 0 ≤ B)
    (hI : I.card ≤ N) (hJ : J.card ≤ N)
    (hf : ∀ i, i ∉ I → f i = 0) (hg : ∀ i, i ∉ J → g i = 0)
    (hB : ∀ i ∈ I ∪ J, ‖c • (f i-g i)‖ ≤ B) :
    ‖c • ((∑ᶠ i, f i)-(∑ᶠ i, g i))‖ ≤ (2*(N : ℝ))*B := by
  classical
  have hF : (∑ᶠ i, f i) = ∑ i ∈ I ∪ J, f i :=
    finsum_eq_sum_of_support_subset f (fun i hi => by
      by_contra hn
      exact hi (hf i (fun h => hn (Finset.mem_union_left J h))))
  have hG : (∑ᶠ i, g i) = ∑ i ∈ I ∪ J, g i :=
    finsum_eq_sum_of_support_subset g (fun i hi => by
      by_contra hn
      exact hi (hg i (fun h => hn (Finset.mem_union_right I h))))
  rw [hF,hG,← Finset.sum_sub_distrib,Finset.smul_sum]
  have hCard : (I ∪ J).card ≤ 2*N := (Finset.card_union_le I J).trans (by omega)
  calc
    _ ≤ ∑ i ∈ I ∪ J, ‖c • (f i-g i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ I ∪ J, B := Finset.sum_le_sum hB
    _ = ((I ∪ J).card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hB0

theorem hasFDerivAt_finsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ι → E → F) (D : ι → E →L[ℝ] F) (I : Finset ι) {x : E}
    (hf : ∀ i, HasFDerivAt (f i) (D i) x)
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0) :
    HasFDerivAt (fun z => ∑ᶠ i, f i z) (∑ᶠ i, D i) x := by
  classical
  have hD (i : ι) (hi : i ∉ I) : D i = 0 := by
    have hz : (f i) =ᶠ[𝓝 x] (fun _ => 0) := hzero.mono (fun z hz => hz i hi)
    exact (hf i).unique ((hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq hz)
  rw [finsum_eq_sum_of_support_subset D (fun i hi => by
    by_contra hn
    exact hi (hD i hn))]
  exact (HasFDerivAt.fun_sum (fun i _ => hf i)).congr_of_eventuallyEq
    (finsum_eventually_eq_sum f I hzero)

theorem hasDerivWithinAt_finsum {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ι → ℝ → F) (D : ι → F) (I : Finset ι) (s : Set ℝ) (t : ℝ)
    (hf : ∀ i ∈ I, HasDerivWithinAt (f i) (D i) s t)
    (hzero : ∀ τ i, i ∉ I → f i τ = 0) (hDzero : ∀ i, i ∉ I → D i = 0) :
    HasDerivWithinAt (fun τ => ∑ᶠ i, f i τ) (∑ᶠ i, D i) s t := by
  classical
  have heq : (fun τ => ∑ᶠ i, f i τ) = (fun τ => ∑ i ∈ I, f i τ) := by
    funext τ
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hn
    exact hi (hzero τ i hn)
  rw [heq,finsum_eq_sum_of_support_subset D (fun i hi => by
    by_contra hn
    exact hi (hDzero i hn))]
  exact HasDerivWithinAt.fun_sum hf

end Yau.LeafProofs.L17LocalizedSchauderAux
