import Yau.Proofs.E02ProjectionPenalty

open Matrix Set Metric
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- A fixed Gram matrix bounds every entry of the actual rectangular
matrix in the native entrywise norm, including empty dimensions. -/
theorem norm_le_of_fixed_gram {n m : ℕ} (A : Herm n) (M : Rect n m) (hM : M*Mᴴ = A) :
    ‖M‖ ≤ |(Matrix.trace A).re|+1 := by
  have hR : 0 ≤ |(Matrix.trace A).re|+1 := by positivity
  apply (Matrix.norm_le_iff hR).mpr
  intro i j
  have hEntry : ‖M i j‖^2 ≤ ∑ k, ∑ l, ‖M k l‖^2 :=
    (Finset.single_le_sum (fun l _ => sq_nonneg ‖M i l‖) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖M k l‖))
        (Finset.mem_univ i))
  have hTrace : (∑ k, ∑ l, ‖M k l‖^2) = (Matrix.trace A).re := by
    rw [←gram_trace_re_eq_sum_norm_sq,Matrix.trace_mul_comm,hM]
  rw [hTrace] at hEntry
  have ht := le_abs_self (Matrix.trace A).re
  have hn := norm_nonneg (M i j)
  have hab := abs_nonneg (Matrix.trace A).re
  nlinarith [sq_nonneg |(Matrix.trace A).re|]

theorem isCompact_fixed_gram {n m : ℕ} (A : Herm n) :
    IsCompact {M : Rect n m | M*Mᴴ = A} := by
  have hClosed : IsClosed {M : Rect n m | M*Mᴴ = A} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : Rect n m) (|(Matrix.trace A).re|+1)).of_isClosed_subset hClosed
  intro M hM
  simpa only [mem_closedBall,dist_zero_right] using norm_le_of_fixed_gram A M hM

/-- The entire fixed-contact equality orbit is compact. No isolated
minimum or choice of unitary parametrization is used. -/
theorem isCompact_equality_orbit {n m : ℕ} (A B : Herm n) (P₀ : Herm m) :
    IsCompact {M : Rect n m | M*Mᴴ = A ∧ Mᴴ*B*M = P₀} := by
  have hSecond : IsClosed {M : Rect n m | Mᴴ*B*M = P₀} :=
    isClosed_eq (by fun_prop) continuous_const
  exact (isCompact_fixed_gram A).inter_right hSecond

end Yau.NodeProofs.E02Aux
