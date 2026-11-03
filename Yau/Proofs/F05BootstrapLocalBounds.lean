import Yau.Proofs.F05BootstrapLocalFields

/-! Finite families of actual local Holder fields have one numerical
budget. Receiving compact caps lie in the original positive-time patch. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_holder_finite_common {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    {α : ℝ} {Q : Set (Point n)} {f : ι → Point n → V}
    (hf : ∀ i, ∃ C : ℝ, 0 < C ∧ HolderBound α Q (f i) C) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, HolderBound α Q (f i) C := by
  classical
  choose c hc hBound using hf
  let C := 1+∑ i,c i
  have hSum : 0 ≤ ∑ i,c i := Finset.sum_nonneg (fun i hi => (hc i).le)
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro i
  have hi : c i ≤ ∑ j,c j := Finset.single_le_sum (fun j hj => (hc j).le) (Finset.mem_univ i)
  exact holderBound_mono_const (hBound i) (by dsimp only [C]; linarith)

theorem F05_region_subset_posSpace (ν : Option (RIdx n)) {r : ℝ} (hr2 : r < 2) :
    region ν r ⊆ F05PosSpace ν := by
  intro x hx
  exact ⟨F05_region_mem_flat hx,by simpa only [Metric.mem_ball,dist_zero_right] using hx.1.trans_lt hr2⟩

theorem F05_receiving_subset_posPatch (ν : Option (RIdx n)) {r s T : ℝ}
    (hr2 : r < 2) (hs : 0 < s) : region ν r ×ˢ Icc s T ⊆ F05PosPatch ν T :=
  fun z hz => ⟨F05_region_subset_posSpace ν hr2 hz.1,hs.trans_le hz.2.1,hz.2.2⟩

end Yau.Proofs.F05Aux
