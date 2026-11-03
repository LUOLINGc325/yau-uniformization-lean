import Yau.Proofs.F05BootstrapGoodPolynomialOrder
import Yau.Proofs.F05BootstrapLocalBounds
import Yau.Proofs.F05ExponentialHolder

/-! Finite polynomial and exponential expressions preserve actual local
parabolic Holder bounds with explicit numerical budgets. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_local_holder_add {ν : Option (RIdx n)} {T α : ℝ} {f g : Point n → ℝ}
    (hf : F05LocalHolder α ν T f) (hg : F05LocalHolder α ν T g) :
    F05LocalHolder α ν T (fun z => f z+g z) := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hCf⟩ := hf r hr hr2 s hs hsT
  obtain ⟨D,hD,hDg⟩ := hg r hr hr2 s hs hsT
  exact ⟨C+D,add_pos hC hD,holderBound_add hCf hDg⟩

theorem F05_local_holder_mul {ν : Option (RIdx n)} {T α : ℝ} {f g : Point n → ℝ}
    (hf : F05LocalHolder α ν T f) (hg : F05LocalHolder α ν T g) :
    F05LocalHolder α ν T (fun z => f z*g z) := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hCf⟩ := hf r hr hr2 s hs hsT
  obtain ⟨D,hD,hDg⟩ := hg r hr hr2 s hs hsT
  exact ⟨2*C*D,mul_pos (mul_pos (by norm_num) hC) hD,holderBound_mul hCf hDg⟩

theorem F05_local_holder_exp_neg {ν : Option (RIdx n)} {T α : ℝ} {u : Point n → ℝ}
    (hu : F05LocalHolder α ν T u) :
    F05LocalHolder α ν T (fun z => Real.exp (-u z)) := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hU⟩ := hu r hr hr2 s hs hsT
  refine ⟨Real.exp C*(1+C),mul_pos (Real.exp_pos _) (by linarith),?_⟩
  exact F05_holder_exp (holderBound_neg hU) (fun z hz =>
    (neg_le_abs (u z)).trans (hU.2.1 z hz))

namespace F05GoodPolynomial

theorem local_holder (P : F05GoodPolynomial n) {ν : Option (RIdx n)} {T α : ℝ}
    {u : Point n → ℝ}
    (hAtoms : ∀ β ∈ P.atoms, F05LocalHolder α ν T (F05GoodWord T β u)) :
    F05LocalHolder α ν T (P.eval T u) := by
  revert hAtoms
  induction P with
  | constant c =>
    intro hAtoms r hr hr2 s hs hsT
    refine ⟨|c|+1,by linarith [abs_nonneg c],?_⟩
    exact holderBound_mono_const (holderBound_const α _ c) (by simpa only [Real.norm_eq_abs] using le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  | atom β => intro hAtoms; exact hAtoms β (by simp only [atoms,List.mem_singleton])
  | add P Q ihP ihQ =>
    intro hAtoms
    exact F05_local_holder_add (ihP (fun β hβ => hAtoms β (List.mem_append_left _ hβ)))
      (ihQ (fun β hβ => hAtoms β (List.mem_append_right _ hβ)))
  | mul P Q ihP ihQ =>
    intro hAtoms
    exact F05_local_holder_mul (ihP (fun β hβ => hAtoms β (List.mem_append_left _ hβ)))
      (ihQ (fun β hβ => hAtoms β (List.mem_append_right _ hβ)))

end F05GoodPolynomial
end Yau.Proofs.F05Aux
