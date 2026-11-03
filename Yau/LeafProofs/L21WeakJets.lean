import Yau.LeafProofs.L21WordEquation

/-! Finite weak graph jets retain the literal input at the empty word.
Extending a jet changes only its newly constructed order. -/

open MeasureTheory
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem locallyL2On_mono {O V : Set (X n)} {u : X n → ℂ}
    (hu : LocallyL2On u O) (hVO : V ⊆ O) : LocallyL2On u V :=
  fun K hK hKV => hu K hK (hKV.trans hVO)

theorem dbarWeakOn_mono {O V : Set (X n)} {A : X n → Matrix (Fin n) (Fin n) ℂ}
    {u : X n → ℂ} {f : X n → Fin n → ℂ} (h : DbarWeakOn A u f O) (hVO : V ⊆ O) :
    DbarWeakOn A u f V := fun i ψ hψ hcψ hsψ => h i ψ hψ hcψ (hsψ.trans hVO)

theorem evalWordTerms_congr (U V : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n))
    (h : ∀ t ∈ L, U t.2 = V t.2) (x : X n) : evalWordTerms U L x = evalWordTerms V L x := by
  unfold evalWordTerms
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [h t ht]

theorem graphWordSource_congr (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (f : X n → Fin n → ℂ) (U V : List (Yau.RIdx n) → X n → ℂ) (q : ℕ)
    (h : ∀ w, w.length ≤ q → U w = V w) (w : List (Yau.RIdx n)) (hw : w.length ≤ q) :
    graphWordSource A f U w = graphWordSource A f V w := by
  funext x i
  unfold graphWordSource
  rw [evalWordTerms_congr U V _ (fun t ht => h t.2 ((correctionTerms_order A i w t ht).trans hw))]

def WeakGraphJet (A : X n → Matrix (Fin n) (Fin n) ℂ) (f : X n → Fin n → ℂ)
    (u : X n → ℂ) (U : List (Yau.RIdx n) → X n → ℂ) (q : ℕ) (O : Set (X n)) : Prop :=
  U [] = u ∧
    (∀ w, w.length ≤ q → LocallyL2On (U w) O) ∧
    (∀ w, w.length < q → ∀ a, ComplexWeakDerivativeOn O (U w) (U (a :: w)) (Yau.realVec a)) ∧
    ∀ w, w.length ≤ q → DbarWeakOn A (U w) (graphWordSource A f U w) O

def initialWordJet (u : X n → ℂ) : List (Yau.RIdx n) → X n → ℂ
  | [] => u
  | _ :: _ => fun _ => 0

theorem initialWordJet_isWeakGraphJet {O : Set (X n)}
    {A : X n → Matrix (Fin n) (Fin n) ℂ} {f : X n → Fin n → ℂ} {u : X n → ℂ}
    (hu : LocallyL2On u O) (heq : DbarWeakOn A u f O) :
    WeakGraphJet A f u (initialWordJet u) 0 O := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro w hw
    have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    exact hu
  · intro w hw
    omega
  · intro w hw
    have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    have hs : graphWordSource A f (initialWordJet u) [] = f := by
      funext x i
      simp only [graphWordSource, wordDerivative, correctionTerms, evalWordTerms_nil, add_zero]
    rw [hs]
    exact heq

def extendWordJet (q : ℕ) (U : List (Yau.RIdx n) → X n → ℂ)
    (G : ∀ w : List (Yau.RIdx n), w.length = q → X n → Yau.RIdx n → ℂ) :
    List (Yau.RIdx n) → X n → ℂ
  | [] => U []
  | a :: w => if h : w.length = q then fun x => G w h x a else U (a :: w)

theorem extendWordJet_old (q : ℕ) (U : List (Yau.RIdx n) → X n → ℂ)
    (G : ∀ w : List (Yau.RIdx n), w.length = q → X n → Yau.RIdx n → ℂ)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) : extendWordJet q U G w = U w := by
  cases w with
  | nil => rfl
  | cons a w =>
    have hn : w.length ≠ q := by simp only [List.length_cons] at hw; omega
    simp only [extendWordJet, dif_neg hn]

theorem extendWordJet_new (q : ℕ) (U : List (Yau.RIdx n) → X n → ℂ)
    (G : ∀ w : List (Yau.RIdx n), w.length = q → X n → Yau.RIdx n → ℂ)
    (w : List (Yau.RIdx n)) (hw : w.length = q) (a : Yau.RIdx n) :
    extendWordJet q U G (a :: w) = fun x => G w hw x a := by
  simp only [extendWordJet, dif_pos hw]

end Yau.LeafProofs.L21Aux
