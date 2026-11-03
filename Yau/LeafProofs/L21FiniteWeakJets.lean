import Yau.LeafProofs.L21WeakJetGain

/-! Smooth coefficients and a locally L² weak solution give actual weak
coordinate jets of every finite order on each fixed inner domain. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem exists_finite_weak_graph_jet {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (u : X n → ℂ) (hu : LocallyL2On u O) (heq : DbarWeakOn A u f O)
    (q : ℕ) {V : Set (X n)} (hV : IsOpen V) (hcV : IsCompact (closure V)) (hVO : closure V ⊆ O) :
    ∃ U : List (Yau.RIdx n) → X n → ℂ, WeakGraphJet A f u U q V := by
  induction q generalizing V with
  | zero =>
    have hVO0 : V ⊆ O := subset_closure.trans hVO
    exact ⟨initialWordJet u, initialWordJet_isWeakGraphJet
      (locallyL2On_mono hu hVO0) (dbarWeakOn_mono heq hVO0)⟩
  | succ q ih =>
    obtain ⟨W, hW, hVW, hWO, hcW⟩ :=
      exists_open_between_and_isCompact_closure hcV hO hVO
    obtain ⟨U, hU⟩ := ih (V := W) hW hcW hWO
    have hWO0 : W ⊆ O := subset_closure.trans hWO
    exact extend_weak_graph_jet hW hV hcV hVW (fun i j => (hA i j).mono hWO0)
      (fun x hx => hsmall x (hWO0 hx)) f (fun i => (hf i).mono hWO0) q u U hU

end Yau.LeafProofs.L21Aux
