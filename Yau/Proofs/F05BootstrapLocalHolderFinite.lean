import Yau.Proofs.F05BootstrapPolynomialHolder
import Yau.LeafProofs.L16MatrixHolder

/-! Finite displayed local Holder families have actual common budgets;
this also assembles a genuine Frobenius matrix Holder field. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_local_holder_const (ν : Option (RIdx n)) (T α c : ℝ) :
    F05LocalHolder α ν T (fun _ => c) := by
  intro r hr hr2 s hs hsT
  exact ⟨|c|+1,by positivity,holderBound_mono_const (holderBound_const α _ c)
    (by simpa only [Real.norm_eq_abs] using le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))⟩

theorem F05_local_holder_list_sum {ι : Type*} (xs : List ι) {ν : Option (RIdx n)}
    {T α : ℝ} {f : ι → Point n → ℝ}
    (hf : ∀ i ∈ xs, F05LocalHolder α ν T (f i)) :
    F05LocalHolder α ν T (fun z => (xs.map (fun i => f i z)).sum) := by
  induction xs with
  | nil => exact F05_local_holder_const ν T α 0
  | cons i xs ih =>
    exact F05_local_holder_add (hf i List.mem_cons_self)
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

theorem F05_local_holder_matrix {ν : Option (RIdx n)} {T α : ℝ} {a : Point n → Mat n}
    (ha : ∀ i j, F05LocalHolder α ν T (fun z => a z i j)) : F05LocalHolder α ν T a := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hEntries⟩ := F05_holder_finite_common (ι := RIdx n × RIdx n)
    (fun ij => ha ij.1 ij.2 r hr hr2 s hs hsT)
  let D := (Fintype.card (RIdx n) : ℝ)^2*C
  refine ⟨D+1,by dsimp only [D]; positivity,?_⟩
  exact holderBound_mono_const (holderBound_matrix_of_entries hC.le (fun i j => hEntries (i,j)))
    (le_add_of_nonneg_right (by norm_num))

end Yau.Proofs.F05Aux
