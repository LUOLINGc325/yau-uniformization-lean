import Yau.Proofs.V03RealizedCurrentAtom

/-! The genuine four coefficient and two velocity contributions form one
finite explicitly signed family, with no dimension-positivity assumption. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

abbrev CurrentExpansionIndex (q : ℕ) :=
  ((((Fin q × Fin q) × Fin q) × Fin 4) ⊕ ((Fin q × Fin q) × Fin 2))

def realizedExpandedAtom {n q : ℕ} {X : KahlerManifold n} (d : VariationData X q)
    (B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) : CurrentExpansionIndex q → ℝ → ℝ
  | .inl t, θ =>
    let i := t.1.1.1
    let k := t.1.1.2
    let c := t.1.2
    if t.2 = 0 then realizedCurrentAtom d B F E l h α (some i) (some k) (.inr ((i, k), (c, 0))) 1 (.inl c) θ
    else if t.2 = 1 then realizedCurrentAtom d B F E l h α (some k) (some i) (.inr ((i, k), (c, 0))) 1 (.inl c) θ
    else if t.2 = 2 then realizedCurrentAtom d B F E l h α (some i) (some k) (.inr ((i, k), (c, 1))) 0 (.inl c) θ
    else -realizedCurrentAtom d B F E l h α (some k) (some i) (.inr ((i, k), (c, 1))) 0 (.inl c) θ
  | .inr t, θ =>
    let i := t.1.1
    let k := t.1.2
    if t.2 = 0 then realizedCurrentAtom d B F E l h α (some k) none (.inl (i, k)) 3 (.inr i) θ
    else realizedCurrentAtom d B F E l h α (some i) none (.inl (i, k)) 1 (.inr k) θ

theorem sum_realizedExpandedAtom {n q : ℕ} {X : KahlerManifold n} (d : VariationData X q)
    (B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (θ : ℝ) :
    (∑ t : CurrentExpansionIndex q, realizedExpandedAtom d B F E l h α t θ) =
      ∑ i : Fin q, ∑ k : Fin q,
        ((∑ c : Fin q,
          (realizedCurrentAtom d B F E l h α (some i) (some k) (.inr ((i, k), (c, 0))) 1 (.inl c) θ +
            realizedCurrentAtom d B F E l h α (some k) (some i) (.inr ((i, k), (c, 0))) 1 (.inl c) θ +
            realizedCurrentAtom d B F E l h α (some i) (some k) (.inr ((i, k), (c, 1))) 0 (.inl c) θ -
            realizedCurrentAtom d B F E l h α (some k) (some i) (.inr ((i, k), (c, 1))) 0 (.inl c) θ)) +
          realizedCurrentAtom d B F E l h α (some k) none (.inl (i, k)) 3 (.inr i) θ +
          realizedCurrentAtom d B F E l h α (some i) none (.inl (i, k)) 1 (.inr k) θ) := by
  simp only [CurrentExpansionIndex, realizedExpandedAtom, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fin.sum_univ_four, Fin.sum_univ_two, Fin.reduceEq, ↓reduceIte,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end Yau.Blueprint.V03Proof
