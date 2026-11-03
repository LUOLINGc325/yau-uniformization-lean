import Yau.Proofs.P03FieldSpanLocus
import Yau.Proofs.P03Evaluation

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The original finite jet interpolation provides one finite global field
family spanning over any prescribed compact set. -/
theorem exists_fields_spanning_on_compact
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → Fin n → MvPolynomial (Fin n) ℂ),
      ∃ V : VectorField M, IsHolomorphicField V ∧ ∀ p ∈ pts, JetAgreeField V p (Pj p) k)
    (K : Set M.Carrier) (hK : IsCompact K) :
    ∃ (L : ℕ) (W : Fin L → VectorField M),
      (∀ l, IsHolomorphicField (W l)) ∧
      ∀ x ∈ K, Submodule.span ℂ (range fun l => W l x) = ⊤ := by
  classical
  choose W hW hspan using fun p : K => field_jets_spanning_at_point hjets p.1
  let O : K → Set M.Carrier := fun p =>
    {x | Submodule.span ℂ (range fun i => W p i x) = ⊤}
  have hopen (p : K) : IsOpen (O p) := isOpen_field_span_locus (W p) (hW p)
  have hcover : K ⊆ ⋃ p, O p := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hspan ⟨x, hx⟩⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover O hopen hcover
  let I := T × Fin n
  let e := Fintype.equivFin I
  let V : Fin (Fintype.card I) → VectorField M := fun j =>
    W (e.symm j).1.1 (e.symm j).2
  refine ⟨Fintype.card I, V, (fun j => hW _ _), ?_⟩
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hT hx)
  change Submodule.span ℂ (range fun i : Fin n => W p i x) = ⊤ at hxp
  have hrange : (range fun i : Fin n => W p i x) ⊆ range fun j => V j x := by
    rintro _ ⟨i, rfl⟩
    refine ⟨e (⟨p, hp⟩, i), ?_⟩
    simp only [V, e.symm_apply_apply]
  apply top_unique
  rw [← hxp]
  exact Submodule.span_mono hrange

end Yau.NodeProofs.P03Aux
