import Yau.Proofs.P03ProjectivePairings
import Yau.Proofs.P03AffineParameterDimensions
import Yau.Proofs.P03AffineSchurAvoidance

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n m L : ℕ}

/-- Small finite affine perturbations avoid every failed span on the entire
spatial open set. The proof uses explicit projective annihilators and row
charts, followed by the native lower-dimensional-image theorem. -/
theorem dense_spanning_affine_parameters (V : E → Fin m → ComplexVector n)
    (W : E → Fin L → ComplexVector n) {U : Set E} (hU : IsOpen U)
    (hV : ∀ j, DifferentiableOn ℝ (fun x => V x j) U)
    (hW : ∀ l, DifferentiableOn ℝ (fun x => W x l) U)
    (hspan : ∀ x ∈ U, Submodule.span ℂ (range (W x)) = ⊤)
    (hd : Module.finrank ℝ E + (n - 1) * 2 < m * 2) :
    Dense {T : Fin m → Fin L → ℂ | ∀ x ∈ U,
      Submodule.span ℂ (range (affineVectorTuple (V x) (W x) T)) = ⊤} := by
  classical
  let D : Fin n × Fin L → Type _ := fun δ =>
    (E × ({i : Fin n // i ≠ δ.1} → ℂ)) × (Fin m → {l : Fin L // l ≠ δ.2} → ℂ)
  let s : ∀ δ : Fin n × Fin L, Set (D δ) := fun δ =>
    {p | p.1 ∈ U ×ˢ univ ∧ spanSchurCoefficients W δ.1 p.1 δ.2 ≠ 0}
  let f : ∀ δ : Fin n × Fin L, D δ → (Fin m → Fin L → ℂ) := fun δ =>
    affineSchurChart (spanSchurCoefficients W δ.1) δ.2 (spanSchurRightHand V δ.1)
  apply dense_good_of_finite_bad_charts D s f
  · intro δ
    exact affineSchurChart_differentiableOn _ δ.2 _ (hU.prod isOpen_univ)
      (spanSchurCoefficients_differentiableOn W hU hW δ.1)
      (spanSchurRightHand_differentiableOn V hU hV δ.1)
  · intro δ
    apply affineRowParameter_finrank_lt δ.2
    simpa only [Module.finrank_prod, projectiveParameters_finrank, Fintype.card_fin] using hd
  · intro T hbad
    change ¬ (∀ x ∈ U,
      Submodule.span ℂ (range (affineVectorTuple (V x) (W x) T)) = ⊤) at hbad
    push_neg at hbad
    obtain ⟨x, hx, hbad⟩ := hbad
    obtain ⟨direction, w, pivot, hp, hT⟩ :=
      affineVectorTuple_bad_span_chart (V x) (W x) (hspan x hx) T hbad
    apply mem_iUnion.mpr
    refine ⟨(direction, pivot), ((x, w), fun j q => T j q.1), ?_, ?_⟩
    · exact ⟨⟨hx, mem_univ _⟩, hp⟩
    · exact hT.symm

end Yau.NodeProofs.P03Aux
