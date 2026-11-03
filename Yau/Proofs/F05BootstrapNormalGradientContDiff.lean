import Yau.Proofs.F05BootstrapNormalFields
import Yau.Proofs.F05BootstrapCoordinateContDiff

/-! The joint order of the value/normal-first-derivative family controls
the full actual spatial gradient of every good word. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_word_gradient_contDiff {T α : ℝ} {k : ℕ} {Q : Set (Point n)}
    (j : RIdx n) (hQ : Q ⊆ F05PosPatch (some j) T) (u : Point n → ℝ)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      F05LocalSchauder α (some j) T (F05GoodWord T γ u))
    (hJoint : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05GoodWord T γ u) Q)
    (hNormal : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05NormalWord T j γ u) Q)
    (β : List (Option (RIdx n))) (hβ : F05GoodList (some j) β) :
    ContDiffOn ℝ k (F05RelD (F05PosSpace (some j)) (F05GoodWord T β u)) Q := by
  classical
  apply F05_covector_contDiff_of_components
  intro i
  by_cases hi : i = j
  · subst i
    exact hNormal β hβ
  · have hGood : F05GoodLetter (some j) (some i) := hi
    have hIβ : F05GoodList (some j) (some i::β) :=
      (F05GoodList_cons (some j) (some i) β).mpr ⟨hGood,hβ⟩
    have hEq := F05_good_gradient_component_eq hGood (hWords β hβ)
    exact (hJoint (some i::β) hIβ).congr (fun z hz => hEq (hQ hz))

end Yau.Proofs.F05Aux
