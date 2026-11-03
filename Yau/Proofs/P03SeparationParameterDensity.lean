import Yau.Proofs.P03AffineParameterDimensions
import Yau.Proofs.P03AffineSchurAvoidance

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

def affineScalarTuple {E : Type*} {m L : ℕ} (V : E → Fin m → ℂ) (W : E → Fin L → ℂ)
    (T : Fin m → Fin L → ℂ) (x : E) : Fin m → ℂ :=
  fun j => V x j + ∑ l, T j l * W x l

/-- Finite affine scalar perturbations avoid simultaneous zeroes throughout
the spatial open set, using exactly the original finite parameter dimension. -/
theorem dense_separating_affine_parameters {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m L : ℕ}
    (V : E → Fin m → ℂ) (W : E → Fin L → ℂ) {U : Set E} (hU : IsOpen U)
    (hV : ∀ j, DifferentiableOn ℝ (fun x => V x j) U)
    (hW : ∀ l, DifferentiableOn ℝ (fun x => W x l) U)
    (honto : ∀ x ∈ U, ∃ l, W x l ≠ 0) (hd : Module.finrank ℝ E < m * 2) :
    Dense {T : Fin m → Fin L → ℂ | ∀ x ∈ U, affineScalarTuple V W T x ≠ 0} := by
  classical
  let D : Fin L → Type _ := fun pivot => E × (Fin m → {l : Fin L // l ≠ pivot} → ℂ)
  let s : ∀ pivot : Fin L, Set (D pivot) := fun pivot => {p | p.1 ∈ U ∧ W p.1 pivot ≠ 0}
  let f : ∀ pivot : Fin L, D pivot → (Fin m → Fin L → ℂ) := fun pivot =>
    affineSchurChart W pivot (fun x j => -V x j)
  apply dense_good_of_finite_bad_charts D s f
  · intro pivot
    exact affineSchurChart_differentiableOn W pivot _ hU hW (fun j => (hV j).neg)
  · intro pivot
    exact affineRowParameter_finrank_lt pivot hd
  · intro T hbad
    change ¬ (∀ x ∈ U, affineScalarTuple V W T x ≠ 0) at hbad
    push_neg at hbad
    obtain ⟨x, hx, hzero⟩ := hbad
    obtain ⟨pivot, hp⟩ := honto x hx
    have hrows : ∀ j, (∑ l, T j l * W x l) = -V x j := by
      intro j
      have hz := congrFun hzero j
      change V x j + ∑ l, T j l * W x l = 0 at hz
      exact eq_neg_of_add_eq_zero_right hz
    have hT := affineSchurRows_cover (W x) pivot hp (fun j => -V x j) T hrows
    apply mem_iUnion.mpr
    exact ⟨pivot, (x, fun j q => T j q.1), ⟨hx, hp⟩, hT.symm⟩

end Yau.NodeProofs.P03Aux
