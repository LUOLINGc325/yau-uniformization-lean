import Yau.Proofs.F05BootstrapLocalBounds
import Yau.LeafProofs.L16Localization

/-! Actual local vector Holder fields are closed under finite sums and
scalar multiplication, with constructed positive numerical budgets. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_local_vector_holder_const (ν : Option (RIdx n)) (T α : ℝ) (c : V) :
    F05LocalHolder α ν T (fun _ => c) := by
  intro r hr hr2 s hs hsT
  exact ⟨‖c‖+1,by positivity,holderBound_mono_const (holderBound_const α _ c)
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))⟩

theorem F05_local_vector_holder_add {ν : Option (RIdx n)} {T α : ℝ} {f g : Point n → V}
    (hf : F05LocalHolder α ν T f) (hg : F05LocalHolder α ν T g) :
    F05LocalHolder α ν T (fun z => f z+g z) := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hF⟩ := hf r hr hr2 s hs hsT
  obtain ⟨D,hD,hG⟩ := hg r hr hr2 s hs hsT
  exact ⟨C+D,add_pos hC hD,holderBound_add hF hG⟩

theorem F05_local_vector_holder_list_sum {ι : Type*} (xs : List ι) {ν : Option (RIdx n)}
    {T α : ℝ} {f : ι → Point n → V}
    (hf : ∀ i ∈ xs, F05LocalHolder α ν T (f i)) :
    F05LocalHolder α ν T (fun z => (xs.map (fun i => f i z)).sum) := by
  induction xs with
  | nil => exact F05_local_vector_holder_const ν T α (0 : V)
  | cons i xs ih =>
    exact F05_local_vector_holder_add (hf i List.mem_cons_self)
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

theorem F05_local_vector_holder_smul {ν : Option (RIdx n)} {T α : ℝ}
    {c : Point n → ℝ} {f : Point n → V} (hc : F05LocalHolder α ν T c)
    (hf : F05LocalHolder α ν T f) : F05LocalHolder α ν T (fun z => c z • f z) := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hScalar⟩ := hc r hr hr2 s hs hsT
  obtain ⟨D,hD,hVector⟩ := hf r hr hr2 s hs hsT
  exact ⟨C*D+C*D,by positivity,holderBound_smul_refined hScalar hVector hC.le hD.le
    (fun z hz => by simpa only [Real.norm_eq_abs] using hScalar.2.1 z hz) hVector.2.1⟩

theorem F05_local_vector_holder_congr {ν : Option (RIdx n)} {T α : ℝ} {f g : Point n → V}
    (hf : F05LocalHolder α ν T f) (hEq : EqOn f g (F05PosPatch ν T)) :
    F05LocalHolder α ν T g := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hBound⟩ := hf r hr hr2 s hs hsT
  exact ⟨C,hC,holderBound_congr_on hBound (fun z hz =>
    hEq (F05_receiving_subset_posPatch ν hr2 hs hz))⟩

end Yau.Proofs.F05Aux
