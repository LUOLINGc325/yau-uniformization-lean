import Yau.Proofs.F05BootstrapGoodDirections

/-! A finite product-rule list records both choices at each good letter.
Every factor word is good and has at most the original finite order. -/

noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

def F05LeibnizSplits {D : Type*} : List D → List (List D × List D)
  | [] => [([],[])]
  | d::β => (F05LeibnizSplits β).flatMap (fun st => [(d::st.1,st.2),(st.1,d::st.2)])

theorem F05_leibniz_splits_properties {ν : Option (RIdx n)}
    {β : List (Option (RIdx n))} (hβ : F05GoodList ν β)
    {st : List (Option (RIdx n)) × List (Option (RIdx n))} (hst : st ∈ F05LeibnizSplits β) :
    F05GoodList ν st.1 ∧ F05GoodList ν st.2 ∧ st.1.length+st.2.length = β.length := by
  induction β generalizing st with
  | nil =>
    have hEq : st = ([],[]) := List.mem_singleton.mp hst
    subst st
    exact ⟨by simp [F05GoodList],by simp [F05GoodList],rfl⟩
  | cons d β ih =>
    have hdβ := (F05GoodList_cons ν d β).mp hβ
    obtain ⟨p,hp,hChoice⟩ := List.mem_flatMap.mp hst
    have hGood := ih hdβ.2 hp
    rcases List.mem_cons.mp hChoice with hEq | hLast
    · subst st
      exact ⟨(F05GoodList_cons ν d p.1).mpr ⟨hdβ.1,hGood.1⟩,hGood.2.1,
        by simp only [List.length_cons]; omega⟩
    · have hEq : st = (p.1,d::p.2) := List.mem_singleton.mp hLast
      subst st
      exact ⟨hGood.1,(F05GoodList_cons ν d p.2).mpr ⟨hdβ.1,hGood.2.1⟩,
        by simp only [List.length_cons]; omega⟩

end Yau.Proofs.F05Aux
