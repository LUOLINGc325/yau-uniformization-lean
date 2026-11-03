import Yau.Proofs.F01CompactTaylorHolder
import Yau.Proofs.F01PositiveMatrixCompactHolder

/-! Every spatial operator jet of the actual inverse-metric principal
symbol has a Holder budget on a fixed positive matrix range. The only
input jets are those of the actual matrix field through the same order. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem scalarSymbol_spatial_jet_holder_budget {ell C : ℝ}
    (hell : 0 < ell) (hC : 0 ≤ C) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β : ℝ)
      (H : Point n → Matrix (Fin n) (Fin n) ℂ),
      IsOpen S → Q ⊆ S ×ˢ (Set.univ : Set ℝ) → HolderBound β Q H C →
      (∀ p ∈ Q, (H p - (ell : ℂ) • 1).PosSemidef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => H (z, p.2)) S) →
      (∀ j : Fin (k + 1),
        HolderBound β Q (fun p => iteratedFDeriv ℝ j.val (fun z => H (z, p.2)) p.1) C) →
      HolderBound β Q
        (fun p => iteratedFDeriv ℝ k (fun z => scalarSymbol (H (z, p.2))) p.1) B := by
  let K : Set (Matrix (Fin n) (Fin n) ℂ) :=
    closedBall 0 C ∩ {H | (H - (ell : ℂ) • 1).PosSemidef}
  let U : Set (Matrix (Fin n) (Fin n) ℂ) := {H | H.det ≠ 0}
  have hClosed : IsClosed {H : Matrix (Fin n) (Fin n) ℂ |
      (H - (ell : ℂ) • 1).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right hClosed
  have hKU : K ⊆ U := by
    intro H hH
    have hp : ((ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)
    have he : (ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (H - (ell : ℂ) • 1) = H := by abel
    have hpos := hp.add_posSemidef hH.2
    rw [he] at hpos
    exact hpos.det_pos.ne'
  obtain ⟨B, hB, hb⟩ := compact_iterated_jet_holder_composition_budget
    (n := n) matrix_nonsingular_domain_isOpen hK (positive_matrix_range_convex ell C)
    hKU scalarSymbol_contDiffOn_nonsingular hC k
  refine ⟨B, hB, ?_⟩
  intro Q S β H hS hQS hH hlo hs hj
  apply hb Q S β H hS hQS ?_ hH hs hj
  intro p hp
  exact ⟨mem_closedBall.mpr (by simpa only [dist_zero_right] using hH.2.1 p hp), hlo p hp⟩

end Yau.NodeProofs.F01Aux
