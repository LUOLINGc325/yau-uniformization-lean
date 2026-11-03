import Yau.Proofs.E02ProjectionPenalty
import Yau.Proofs.G04SpectralBounds

open Matrix Set Metric
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem posSemidef_square_trace_le_trace_sq {n : ℕ} (K : Herm n) (hK : K.PosSemidef) :
    (Matrix.trace (K^2)).re ≤ ((Matrix.trace K).re)^2 := by
  rw [G04Aux.hermitian_square_trace K hK.isHermitian,
    hK.isHermitian.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hK.eigenvalues_nonneg i)

/-- Positive semidefinite matrices with bounded trace are genuinely
bounded in the native matrix norm. -/
theorem norm_le_trace_of_posSemidef {n : ℕ} (K : Herm n) (hK : K.PosSemidef) :
    ‖K‖ ≤ (Matrix.trace K).re := by
  have ht : 0 ≤ (Matrix.trace K).re := (RCLike.nonneg_iff.mp hK.trace_nonneg).1
  apply (Matrix.norm_le_iff ht).mpr
  intro i j
  have hEntry : ‖K i j‖^2 ≤ ∑ k, ∑ l, ‖K k l‖^2 :=
    (Finset.single_le_sum (fun l _ => sq_nonneg ‖K i l‖) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖K k l‖))
        (Finset.mem_univ i))
  rw [←gram_trace_re_eq_sum_norm_sq,hK.isHermitian.eq,←pow_two] at hEntry
  have hSq := posSemidef_square_trace_le_trace_sq K hK
  have hn := norm_nonneg (K i j)
  nlinarith

def psdTraceCone (n : ℕ) (C : ℝ) : Set (Herm n) :=
  {K | K.PosSemidef ∧ (Matrix.trace K).re ≤ C}

theorem isCompact_psdTraceCone (n : ℕ) (C : ℝ) : IsCompact (psdTraceCone n C) := by
  have hTrace : Continuous (fun K : Herm n => (Matrix.trace K).re) := by
    simp only [Matrix.trace,Matrix.diag]
    fun_prop
  have hClosed : IsClosed (psdTraceCone n C) :=
    Matrix.posSemidef_is_closed.inter (isClosed_le hTrace continuous_const)
  apply (isCompact_closedBall (0 : Herm n) (|C|+1)).of_isClosed_subset hClosed
  intro K hK
  change dist K 0 ≤ |C|+1
  rw [dist_zero_right]
  exact (norm_le_trace_of_posSemidef K hK.1).trans (hK.2.trans (by linarith [le_abs_self C]))

end Yau.NodeProofs.E02Aux
