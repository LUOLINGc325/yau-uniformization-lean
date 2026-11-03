import Yau.Proofs.F05BootstrapGoodCorrectionHolder
import Yau.Proofs.F05BootstrapGoodSourceAlgebra
import Yau.Proofs.F05BootstrapLocalHolderFinite

/-! All Holder data for the differentiated finite source are derived
from coefficient value words and current solution Schauder words. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_source_local_holder {ν : Option (RIdx n)} {T α : ℝ}
    (β : List (Option (RIdx n))) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (f u : Point n → ℝ)
    (hf : F05LocalHolder α ν T (F05GoodWord T β f))
    (ha : ∀ st ∈ commutatorSplits β, F05LocalHolder α ν T (F05GoodWord T st.1 a))
    (hb : ∀ st ∈ commutatorSplits β, ∀ j,
      F05LocalHolder α ν T (F05GoodWord T st.1 (fun z => b z j)))
    (hu : ∀ st ∈ commutatorSplits β, F05LocalSchauder α ν T (F05GoodWord T st.2 u)) :
    F05LocalHolder α ν T (F05GoodSource T (F05PosSpace ν) a b f u β) := by
  exact F05_local_holder_add hf (F05_local_holder_list_sum (commutatorSplits β)
    (fun st hst => F05_good_correction_local_holder st.1 st.2 a b u
      (ha st hst) (hb st hst) (hu st hst)))

theorem F05_good_source_derivative_local_holder {ν d : Option (RIdx n)} {T α : ℝ}
    (hd : F05GoodLetter ν d) (β : List (Option (RIdx n))) (hβ : F05GoodList ν β)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ)
    (ha : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length+1 → F05GoodList ν γ →
      F05LocalHolder α ν T (F05GoodWord T γ a))
    (hb : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length+1 → F05GoodList ν γ → ∀ j,
      F05LocalHolder α ν T (F05GoodWord T γ (fun z => b z j)))
    (hf : F05LocalHolder α ν T (F05GoodWord T (d::β) f))
    (hCurrent : ∀ γ : List (Option (RIdx n)), γ.length ≤ β.length → F05GoodList ν γ →
      F05LocalSchauder α ν T (F05GoodWord T γ u)) :
    F05LocalHolder α ν T (F05GoodSourceDerivative T d (F05PosSpace ν) a b f u β) := by
  apply F05_local_holder_add hf
  apply F05_local_holder_list_sum (commutatorSplits β)
  intro st hst
  have hLength := (commutatorSplits_properties β st hst).2
  have hLower := commutatorSplits_lower_length β st hst
  have hGood := F05_commutator_splits_good hβ hst
  have hDs : F05GoodList ν (d::st.1) := (F05GoodList_cons ν d st.1).mpr ⟨hd,hGood.1⟩
  have hDt : F05GoodList ν (d::st.2) := (F05GoodList_cons ν d st.2).mpr ⟨hd,hGood.2⟩
  apply F05_local_holder_add
  · exact F05_good_correction_local_holder (d::st.1) st.2 a b u
      (ha _ (by simp only [List.length_cons]; omega) hDs)
      (hb _ (by simp only [List.length_cons]; omega) hDs)
      (hCurrent _ (by omega) hGood.2)
  · exact F05_good_correction_local_holder st.1 (d::st.2) a b u
      (ha _ (by omega) hGood.1) (hb _ (by omega) hGood.1)
      (hCurrent _ (by simp only [List.length_cons]; omega) hDt)

end Yau.Proofs.F05Aux
