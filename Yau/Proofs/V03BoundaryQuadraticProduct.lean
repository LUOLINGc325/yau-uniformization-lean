import Yau.Proofs.V03BoundarySum
import Yau.Proofs.V03BoundaryDifference
import Yau.Proofs.V03RectEntries
import Yau.Proofs.V03BoundaryMatrixVector

/-! Original half-order estimates for a genuine finite-dimensional
quadratic contraction, without any finite-energy or positive-rank premise. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem quadraticForm_eq_sum {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (B *ᵥ v) = ∑ bc : ι × ι, star (v bc.1) * B bc.1 bc.2 * v bc.2 := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Fintype.sum_prod_type, Pi.star_apply, mul_assoc]

theorem boundaryDSq_quadratic_uniform {ι : Type*} [Fintype ι] (L M : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ℝ → ι → ℂ) (B : ℝ → Matrix ι ι ℂ),
      (∀ i, Continuous (fun θ => v θ i)) →
      (∀ b c, Continuous (fun θ => B θ b c)) →
      (∀ i, Function.Periodic (fun θ => v θ i) (2 * Real.pi)) →
      (∀ b c, Function.Periodic (fun θ => B θ b c) (2 * Real.pi)) →
      (∀ θ i, ‖v θ i‖ ≤ L) → (∀ θ b c, ‖B θ b c‖ ≤ M) →
      boundaryDSq (fun θ (_ : Unit) => star (v θ) ⬝ᵥ (B θ *ᵥ v θ)) ≤
        ENNReal.ofReal C * (boundaryDSq v + matrixDSq B) := by
  let A : ENNReal := ENNReal.ofReal (2 * L ^ 2)
  let N : ENNReal := ENNReal.ofReal (2 * M ^ 2)
  let P : ENNReal := ENNReal.ofReal (2 * (L * M) ^ 2)
  let D₀ : ENNReal := A * (N + A) + P
  let D : ENNReal := (Fintype.card (ι × ι) : ENNReal) ^ 2 * D₀
  have hD : D ≠ ⊤ := by dsimp only [D, D₀, A, N, P]; finiteness
  refine ⟨D.toReal, ENNReal.toReal_nonneg, fun v B hv hB hvp hBp hvL hBM => ?_⟩
  let S : ENNReal := boundaryDSq v + matrixDSq B
  have hvi (i : ι) : boundaryDSq (fun θ (_ : Unit) => v θ i) ≤ S :=
    (boundaryDSq_component_le v i).trans (le_add_right le_rfl)
  have hBij (b c : ι) : boundaryDSq (fun θ (_ : Unit) => B θ b c) ≤ S :=
    (matrixDSq_entry_le B b c).trans (le_add_left le_rfl)
  have hstar (b : ι) : Function.Periodic (fun θ => star (v θ b)) (2 * Real.pi) :=
    fun θ => congrArg star (hvp b θ)
  have hentry (b c : ι) : boundaryDSq
      (fun θ (_ : Unit) => star (v θ b) * B θ b c * v θ c) ≤ D₀ * S := by
    have hsp : Function.Periodic (fun θ => star (v θ b)) (2 * Real.pi) :=
      fun θ => congrArg star (hvp b θ)
    have hprod := boundaryDSq_mul_le (hv b).star (hB b c) hsp (hBp b c) hL hM
      (fun θ => by simpa only [norm_star] using hvL θ b) (fun θ => hBM θ b c)
    rw [scalarDSq_conj (hv b) (hvp b)] at hprod
    have hprodS : boundaryDSq (fun θ (_ : Unit) => star (v θ b) * B θ b c) ≤ N * S + A * S := by
      apply hprod.trans
      gcongr
      · exact hvi b
      · exact hBij b c
    have hprod₂ := boundaryDSq_mul_le (u := fun θ => star (v θ b) * B θ b c)
      (v := fun θ => v θ c) ((hv b).star.mul (hB b c)) (hv c)
      (hsp.mul (hBp b c)) (hvp c) (mul_nonneg hL hM) hL
      (fun θ => by rw [norm_mul, norm_star]; exact mul_le_mul (hvL θ b) (hBM θ b c) (norm_nonneg _) hL)
      (fun θ => hvL θ c)
    calc
      _ ≤ A * (N * S + A * S) + P * S := by
        apply hprod₂.trans
        gcongr
        exact hvi c
      _ = _ := by dsimp only [D₀]; ring
  rw [ENNReal.ofReal_toReal hD]
  simp_rw [quadraticForm_eq_sum]
  calc
    _ ≤ (Fintype.card (ι × ι) : ENNReal) * ∑ bc : ι × ι,
        boundaryDSq (fun θ (_ : Unit) => star (v θ bc.1) * B θ bc.1 bc.2 * v θ bc.2) :=
      boundaryDSq_sum_le
        (fun bc => ((hv bc.1).star.mul (hB bc.1 bc.2)).mul (hv bc.2))
        (fun bc => ((hstar bc.1).mul (hBp bc.1 bc.2)).mul (hvp bc.2))
    _ ≤ (Fintype.card (ι × ι) : ENNReal) * ∑ _bc : ι × ι, D₀ * S := by
      gcongr with bc
      exact hentry bc.1 bc.2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [D]
      ring

end Yau.Blueprint.V03Proof
