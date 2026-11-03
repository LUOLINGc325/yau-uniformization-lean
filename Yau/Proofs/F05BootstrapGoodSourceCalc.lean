import Yau.Proofs.F05BootstrapGoodCorrectionCalc
import Yau.Proofs.F05BootstrapGoodSourceAlgebra

/-! The computed finite source has its actual good derivative. Each
Hessian differentiation is justified by the shorter-word rectangle
calculus, and the resulting expression is the literal source recursion. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_source_calculus {ν d : Option (RIdx n)} {T α : ℝ}
    (hd : F05GoodLetter ν d) (β : List (Option (RIdx n)))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ)
    (hF : F05GoodDiffOn T d (F05GoodWord T β f) (F05PosPatch ν T))
    (hA : ∀ st ∈ commutatorSplits β,
      F05GoodDiffOn T d (F05GoodWord T st.1 a) (F05PosPatch ν T))
    (hB : ∀ st ∈ commutatorSplits β, ∀ j,
      F05GoodDiffOn T d (F05GoodWord T st.1 (fun z => b z j)) (F05PosPatch ν T))
    (hU : ∀ st ∈ commutatorSplits β,
      F05LocalSchauder α ν T (F05GoodWord T st.2 u) ∧
      F05LocalSchauder α ν T (F05GoodWord T (d::st.2) u)) :
    F05GoodDiffOn T d (F05GoodSource T (F05PosSpace ν) a b f u β) (F05PosPatch ν T) ∧
      EqOn (F05GoodPartial T d (F05GoodSource T (F05PosSpace ν) a b f u β))
        (F05GoodSourceDerivative T d (F05PosSpace ν) a b f u β) (F05PosPatch ν T) := by
  have hEach (st : List (Option (RIdx n)) × List (Option (RIdx n)))
      (hst : st ∈ commutatorSplits β) :=
    F05_good_correction_calculus hd st.1 st.2 a b u (hA st hst) (hB st hst)
      (hU st hst).1 (hU st hst).2
  have hSum := F05_good_diff_list_sum (commutatorSplits β) (fun st hst => (hEach st hst).1)
  refine ⟨F05_good_diff_add hF hSum,?_⟩
  intro z hz
  change F05GoodPartial T d (fun p => F05GoodWord T β f p+
    ((commutatorSplits β).map (fun st => F05GoodCorrection T (F05PosSpace ν) a b u st.1 st.2 p)).sum) z = _
  rw [F05_good_partial_add hF hSum hz,
    F05_good_partial_list_sum (commutatorSplits β) (fun st hst => (hEach st hst).1) hz]
  change F05GoodWord T (d::β) f z+_ = F05GoodWord T (d::β) f z+_
  congr 1
  apply congrArg List.sum
  exact List.map_congr_left (fun st hst => (hEach st hst).2 hz)

theorem F05_good_source_calculus_finite {ν d : Option (RIdx n)} {T α : ℝ}
    (hd : F05GoodLetter ν d) (β : List (Option (RIdx n))) (hβ : F05GoodList ν β)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ)
    (hA : ∀ γ, γ.length ≤ β.length → F05GoodList ν γ →
      F05GoodDiffOn T d (F05GoodWord T γ a) (F05PosPatch ν T))
    (hB : ∀ γ, γ.length ≤ β.length → F05GoodList ν γ → ∀ j,
      F05GoodDiffOn T d (F05GoodWord T γ (fun z => b z j)) (F05PosPatch ν T))
    (hF : F05GoodDiffOn T d (F05GoodWord T β f) (F05PosPatch ν T))
    (hCurrent : ∀ γ, γ.length ≤ β.length → F05GoodList ν γ →
      F05LocalSchauder α ν T (F05GoodWord T γ u)) :
    F05GoodDiffOn T d (F05GoodSource T (F05PosSpace ν) a b f u β) (F05PosPatch ν T) ∧
      EqOn (F05GoodPartial T d (F05GoodSource T (F05PosSpace ν) a b f u β))
        (F05GoodSourceDerivative T d (F05PosSpace ν) a b f u β) (F05PosPatch ν T) := by
  apply F05_good_source_calculus hd β a b f u hF
  · intro st hst
    have hLength := (commutatorSplits_properties β st hst).2
    exact hA st.1 (by omega) (F05_commutator_splits_good hβ hst).1
  · intro st hst j
    have hLength := (commutatorSplits_properties β st hst).2
    exact hB st.1 (by omega) (F05_commutator_splits_good hβ hst).1 j
  · intro st hst
    have hLength := commutatorSplits_lower_length β st hst
    have hGood := F05_commutator_splits_good hβ hst
    exact ⟨hCurrent st.2 (by omega) hGood.2,
      hCurrent (d::st.2) (by simp only [List.length_cons]; omega)
        ((F05GoodList_cons ν d st.2).mpr ⟨hd,hGood.2⟩)⟩

end Yau.Proofs.F05Aux
