import Yau.Proofs.C01TraceQuadraticAlgebra

/-! A positive metric trace of a strictly positive real quadratic form
is strictly positive in positive dimension. -/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

theorem trace_mul_pos_of_real_quadratics {n : ℕ} (hn : 0 < n)
    (H A : Herm n) (hH : H.PosDef)
    (hA : ∀ v : Fin n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (A *ᵥ v)).re) :
    0 < (Matrix.trace (H * A)).re := by
  let B := CFC.sqrt H
  have hB : B.IsHermitian :=
    ((Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg H)).1
  have hsq : B * B = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hcolumn : ∃ i : Fin n, (fun j => B j i) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hz : B = 0 := by
      ext i j
      exact congrFun (hall j) i
    have hHz : H = 0 := by rw [← hsq, hz, Matrix.zero_mul]
    have hp : 0 < H ⟨0, hn⟩ ⟨0, hn⟩ := hH.diag_pos
    simpa only [hHz, Matrix.zero_apply, lt_self_iff_false] using hp
  have htrace : Matrix.trace (H * A) = Matrix.trace (B * A * B) := by
    rw [Matrix.trace_mul_cycle, hsq, Matrix.trace_mul_comm]
  rw [htrace, trace_congruence_eq_column_quadratics B A hB]
  have hre := Complex.re_sum Finset.univ
    (fun i => star (fun j => B j i) ⬝ᵥ (A *ᵥ (fun j => B j i)))
  rw [hre]
  apply Finset.sum_pos'
  · intro i _
    by_cases hi : (fun j => B j i) = 0
    · simp only [hi, star_zero, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re, le_refl]
    · exact (hA _ hi).le
  · obtain ⟨i, hi⟩ := hcolumn
    exact ⟨i, Finset.mem_univ _, hA _ hi⟩

end Yau.NodeProofs.C01Aux
