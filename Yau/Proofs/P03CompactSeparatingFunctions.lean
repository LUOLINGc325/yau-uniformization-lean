import Yau.Proofs.P03Evaluation

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The original two-point interpolation yields one finite family of global
holomorphic functions distinguishing every pair in a prescribed compact
subset of the actual off-diagonal. -/
theorem exists_functions_separating_on_compact
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k)
    (C : Set (M.Carrier × M.Carrier)) (hC : IsCompact C)
    (hne : ∀ p ∈ C, p.1 ≠ p.2) :
    ∃ (L : ℕ) (h : Fin L → M.Carrier → ℂ),
      (∀ l, IsHolomorphicFn (h l)) ∧
      ∀ p ∈ C, ∃ l, h l p.1 - h l p.2 ≠ 0 := by
  classical
  choose f hf hfx hfy using fun p : C => scalar_jets_separate_points hjets (hne p.1 p.2)
  let O : C → Set (M.Carrier × M.Carrier) := fun p =>
    {q | f p q.1 - f p q.2 ≠ 0}
  have hopen (p : C) : IsOpen (O p) := by
    have ho : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    exact ho.preimage (((hf p).continuous.comp continuous_fst).sub
      ((hf p).continuous.comp continuous_snd))
  have hcover : C ⊆ ⋃ p, O p := by
    intro q hq
    apply mem_iUnion.mpr
    refine ⟨⟨q, hq⟩, ?_⟩
    change f ⟨q, hq⟩ q.1 - f ⟨q, hq⟩ q.2 ≠ 0
    rw [hfx, hfy]
    norm_num
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover O hopen hcover
  let e := Fintype.equivFin T
  let h : Fin (Fintype.card T) → M.Carrier → ℂ := fun j => f (e.symm j).1
  refine ⟨Fintype.card T, h, (fun j => hf _), ?_⟩
  intro q hq
  obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.mp (hT hq)
  change f p q.1 - f p q.2 ≠ 0 at hqp
  refine ⟨e ⟨p, hp⟩, ?_⟩
  simpa only [h, e.symm_apply_apply] using hqp

end Yau.NodeProofs.P03Aux
