import Yau.Proofs.F05BootstrapGoodDirections

/-! The differentiated source uses the literal finite commutator list.
Its exact recursion and good-letter/order properties are algebraic facts. -/

noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05GoodSourceDerivative (T : ℝ) (d : Option (RIdx n)) (X : Set (Space n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ)
    (β : List (Option (RIdx n))) (z : Point n) : ℝ :=
  F05GoodWord T (d::β) f z+((commutatorSplits β).map (fun st =>
    F05GoodCorrection T X a b u (d::st.1) st.2 z+
      F05GoodCorrection T X a b u st.1 (d::st.2) z)).sum

theorem F05_good_source_cons (T : ℝ) (d : Option (RIdx n)) (X : Set (Space n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ)
    (β : List (Option (RIdx n))) :
    F05GoodSource T X a b f u (d::β) = fun z =>
      F05GoodSourceDerivative T d X a b f u β z+F05GoodCorrection T X a b u [d] β z := by
  funext z
  simp only [F05GoodSource,F05GoodSourceDerivative,commutatorSplits,List.map_cons,List.sum_cons,
    List.map_flatMap,List.map_nil]
  rw [list_sum_flatMap_pairs]
  ring

theorem F05_good_source_nil (T : ℝ) (X : Set (Space n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ) :
    F05GoodSource T X a b f u [] = f := by
  funext z
  simp only [F05GoodSource,commutatorSplits,List.map_nil,List.sum_nil,F05GoodWord,add_zero]

theorem F05_commutator_splits_good {ν : Option (RIdx n)}
    {β : List (Option (RIdx n))} (hβ : F05GoodList ν β)
    {st : List (Option (RIdx n)) × List (Option (RIdx n))} (hst : st ∈ commutatorSplits β) :
    F05GoodList ν st.1 ∧ F05GoodList ν st.2 := by
  induction β generalizing st with
  | nil => simp only [commutatorSplits,List.not_mem_nil] at hst
  | cons d β ih =>
    have hdβ := (F05GoodList_cons ν d β).mp hβ
    rcases List.mem_cons.mp hst with hEq | hRest
    · subst st
      exact ⟨(F05GoodList_cons ν d []).mpr ⟨hdβ.1,by simp [F05GoodList]⟩,hdβ.2⟩
    · obtain ⟨p,hp,hChoice⟩ := List.mem_flatMap.mp hRest
      have hGood := ih hdβ.2 hp
      rcases List.mem_cons.mp hChoice with hEq | hLast
      · subst st
        exact ⟨(F05GoodList_cons ν d p.1).mpr ⟨hdβ.1,hGood.1⟩,hGood.2⟩
      · have hEq : st = (p.1,d::p.2) := List.mem_singleton.mp hLast
        subst st
        exact ⟨hGood.1,(F05GoodList_cons ν d p.2).mpr ⟨hdβ.1,hGood.2⟩⟩

end Yau.Proofs.F05Aux
