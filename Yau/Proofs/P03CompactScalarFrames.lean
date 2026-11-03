import Yau.Proofs.P03ScalarDerivativeRows
import Yau.Proofs.P03SpanContinuity

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Original scalar first jets provide finitely many global functions whose
actual chart differentials span throughout a prescribed compact chart set. -/
theorem exists_functions_derivatives_spanning_on_chart_compact
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ chartTarget a) :
    ∃ (L : ℕ) (h : Fin L → holomorphicFunctions M),
      ∀ z ∈ K, Submodule.span ℂ
        (range fun l => functionDerivativeCoordinates (h l) a z) = ⊤ := by
  classical
  have hpoint (z : K) : ∃ f : Fin n → holomorphicFunctions M,
      Submodule.span ℂ (range fun j => functionDerivativeCoordinates (f j) a z.1) = ⊤ := by
    have hz := hsub z.2
    obtain ⟨f, hf⟩ := scalar_jets_injective_chart_differentials hjets a
      (chartInv a z.1) ((extChartAt (ComplexModel n) a).map_target hz)
    have hi : chartPt a (chartInv a z.1) = z.1 :=
      (extChartAt (ComplexModel n) a).right_inv hz
    rw [hi] at hf
    exact ⟨f, (derivativeRows_span_top_iff_tupleDerivative_injective f a z).mpr hf⟩
  choose f hf using hpoint
  let O : K → Set (ComplexVector n) := fun p => chartTarget a ∩
    {z | Submodule.span ℂ (range fun j => functionDerivativeCoordinates (f p j) a z) = ⊤}
  have hopen (p : K) : IsOpen (O p) :=
    isOpen_finite_span_top_inter _ (isOpen_extChartAt_target a)
      (fun j => (functionDerivativeCoordinates_differentiableOn (f p j) a).continuousOn)
  have hcover : K ⊆ ⋃ p, O p := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hsub hz, hf ⟨z, hz⟩⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover O hopen hcover
  let I := T × Fin n
  let e := Fintype.equivFin I
  let h : Fin (Fintype.card I) → holomorphicFunctions M := fun j =>
    f (e.symm j).1.1 (e.symm j).2
  refine ⟨Fintype.card I, h, ?_⟩
  intro z hz
  obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp (hT hz)
  change z ∈ chartTarget a ∧ Submodule.span ℂ
    (range fun j => functionDerivativeCoordinates (f p j) a z) = ⊤ at hzp
  have hrange : (range fun j : Fin n => functionDerivativeCoordinates (f p j) a z) ⊆
      range fun j => functionDerivativeCoordinates (h j) a z := by
    rintro _ ⟨j, rfl⟩
    refine ⟨e (⟨p, hp⟩, j), ?_⟩
    simp only [h, e.symm_apply_apply]
  apply top_unique
  rw [← hzp.2]
  exact Submodule.span_mono hrange

end Yau.NodeProofs.P03Aux
