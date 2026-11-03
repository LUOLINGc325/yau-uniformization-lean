import Yau.Proofs.F01ScalarSymbolSmooth
import Yau.Proofs.F01CompactSmoothHolder

/-! A numerical Holder bound and the genuine positive lower matrix order
give the canonical scalar symbol one Holder constant before all fields.
The proof uses the actual compact convex positive matrix range. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem positive_matrix_range_convex (ell R : ℝ) :
    Convex ℝ (closedBall (0 : Matrix (Fin n) (Fin n) ℂ) R ∩
      {H | (H - (ell : ℂ) • 1).PosSemidef}) := by
  apply (convex_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) R).inter
  intro H hH K hK a b ha hb hab
  have h := (hH.smul ha).add (hK.smul hb)
  have he : a • (H - (ell : ℂ) • 1) + b • (K - (ell : ℂ) • 1) =
      a • H + b • K - (ell : ℂ) • 1 := by
    rw [smul_sub, smul_sub]
    calc
      _ = (a • H + b • K) - (a • ((ell : ℂ) • 1) + b • ((ell : ℂ) • 1)) := by abel
      _ = _ := by rw [← add_smul, hab, one_smul]
  rw [he] at h
  exact h

theorem scalarSymbol_holder_budget {ell C : ℝ} (hell : 0 < ell) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (β : ℝ)
      (H : Point n → Matrix (Fin n) (Fin n) ℂ),
      HolderBound β Q H C →
      (∀ p ∈ Q, (H p - (ell : ℂ) • 1).PosSemidef) →
      HolderBound β Q (fun p => scalarSymbol (H p)) B := by
  let K : Set (Matrix (Fin n) (Fin n) ℂ) :=
    closedBall 0 C ∩ {H | (H - (ell : ℂ) • 1).PosSemidef}
  let U : Set (Matrix (Fin n) (Fin n) ℂ) := {H | H.det ≠ 0}
  have hclosed : IsClosed {H : Matrix (Fin n) (Fin n) ℂ | (H - (ell : ℂ) • 1).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)
  have hK : IsCompact K := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) C).inter_right hclosed
  have hKU : K ⊆ U := by
    intro H hH
    have hp : ((ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)
    have hsum := hp.add_posSemidef hH.2
    have he : (ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (H - (ell : ℂ) • 1) = H := by abel
    rw [he] at hsum
    exact hsum.det_pos.ne'
  obtain ⟨B, hB, hb⟩ := compact_smooth_holder_composition_budget
    matrix_nonsingular_domain_isOpen hK (positive_matrix_range_convex ell C) hKU
    scalarSymbol_contDiffOn_nonsingular hC
  refine ⟨B, hB, ?_⟩
  intro Q β H hf hlo
  apply hb Q β H hf
  intro p hp
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hf.2.1 p hp, hlo p hp⟩

end Yau.NodeProofs.F01Aux
