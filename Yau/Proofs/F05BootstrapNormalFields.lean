import Yau.Proofs.F05BootstrapGoodSpatialJets

/-! Every off-normal Hessian entry is a good successor of the value or
normal-first-derivative family. Only the pure normal entry remains for
the exact differentiated PDE recursion. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

def F05NormalWord (T : ℝ) (j : RIdx n) (β : List (Option (RIdx n)))
    (u : Point n → ℝ) (z : Point n) : ℝ :=
  F05RelD (F05PosSpace (some j)) (F05GoodWord T β u) z (realVec j)

theorem F05_off_normal_hessian_contDiff {T α : ℝ} {k : ℕ} {Q : Set (Point n)}
    (j : RIdx n) (hQ : Q ⊆ F05PosPatch (some j) T) (u : Point n → ℝ)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      F05LocalSchauder α (some j) T (F05GoodWord T γ u))
    (hJoint : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05GoodWord T γ u) Q)
    (hNormal : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05NormalWord T j γ u) Q)
    (β : List (Option (RIdx n))) (hβ : F05GoodList (some j) β)
    (i l : RIdx n) (hOff : i ≠ j ∨ l ≠ j) :
    ContDiffOn ℝ k (fun z => F05RelDD (F05PosSpace (some j)) (F05GoodWord T β u) z
      (realVec i) (realVec l)) Q := by
  classical
  have hU := hWords β hβ
  by_cases hi : i = j
  · subst i
    have hl : l ≠ j := hOff.resolve_left (not_not.mpr rfl)
    have hGoodL : F05GoodLetter (some j) (some l) := hl
    have hLβ : F05GoodList (some j) (some l::β) :=
      (F05GoodList_cons (some j) (some l) β).mpr ⟨hGoodL,hβ⟩
    have hFirst := F05_good_hessian_first_eq hGoodL hU (hWords (some l::β) hLβ)
    apply (hNormal (some l::β) hLβ).congr
    intro z hz
    change F05RelDD (F05PosSpace (some j)) (F05GoodWord T β u) z (realVec j) (realVec l) = _
    rw [F05_relative_hessian_symmetric (F05_local_schauder_to_relative hU) (hQ hz)]
    exact congrArg (fun L : Space n →L[ℝ] ℝ => L (realVec j)) (hFirst (hQ hz))
  · have hGoodI : F05GoodLetter (some j) (some i) := hi
    have hIβ : F05GoodList (some j) (some i::β) :=
      (F05GoodList_cons (some j) (some i) β).mpr ⟨hGoodI,hβ⟩
    have hUi := hWords (some i::β) hIβ
    have hFirst := F05_good_hessian_first_eq hGoodI hU hUi
    by_cases hl : l = j
    · subst l
      apply (hNormal (some i::β) hIβ).congr
      intro z hz
      exact congrArg (fun L : Space n →L[ℝ] ℝ => L (realVec j)) (hFirst (hQ hz))
    · have hGoodL : F05GoodLetter (some j) (some l) := hl
      have hLIβ : F05GoodList (some j) (some l::some i::β) :=
        (F05GoodList_cons (some j) (some l) (some i::β)).mpr ⟨hGoodL,hIβ⟩
      have hGradient := F05_good_gradient_component_eq hGoodL hUi
      apply (hJoint (some l::some i::β) hLIβ).congr
      intro z hz
      exact (congrArg (fun L : Space n →L[ℝ] ℝ => L (realVec l)) (hFirst (hQ hz))).trans
        (hGradient (hQ hz))

end Yau.Proofs.F05Aux
