import Yau.Proofs.D06BoundaryFactors
import Yau.Proofs.D06WeightedFourier

/-! All Fourier coefficients of the original boundary Gram matrix are those
of the identity, using the actual weighted wandering basis. -/

open scoped ComplexOrder ComplexConjugate Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyMatrix_gram_entry (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r → HardySeq r) (t : HardyCircle) (i j : Fin r) :
    ((hardyMatrixTrace a t)ᴴ * L t * hardyMatrixTrace a t) i j =
      hardyWeightedPoint L (a i) (a j) t := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_assoc,
    hardyMatrixTrace, hardyWeightedPoint]

variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem hardyPColumns_shift (n : ℕ) (j : Fin r) :
    (hardyShiftLI ^ n) (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j) =
      hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper
        (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) 1) := by
  have h := hardyOperator_single (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper)
    (hardyFactorOperator_shift L hLp hHerm m hm hLower M hM hUpper) n j 1
  simpa only [one_smul, hardyPColumns] using h.symm

theorem hardyPGram_memLp_top (i j : Fin r) :
    MemLp (hardyWeightedPoint L
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i)
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j)) ⊤ hardyCircleMeasure := by
  unfold hardyWeightedPoint
  apply memLp_finsetSum (p := ⊤) _
  intro k _
  apply memLp_finsetSum (p := ⊤) _
  intro l _
  have hf : MemLp (fun t => star (hardyTraceLp
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i) k t) * L t k l) ⊤ hardyCircleMeasure :=
    (hardyPTrace_memLp L hLp hHerm m hm hLower M hM hUpper k i).star.fun_mul (hLp k l)
  exact hf.fun_mul (hardyPTrace_memLp L hLp hHerm m hm hLower M hM hUpper l j)

theorem hardyPGram_fourier_nat (i j : Fin r) (n : ℕ) :
    fourierCoeff (hardyWeightedPoint L
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i)
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j)) (n : ℤ) =
      if n = 0 ∧ i = j then 1 else 0 := by
  rw [← hardyWeightedInner_shift_left_fourier L hLp, hardyPColumns_shift]
  rw [hardyPColumns, hardyConst_single, hardyFactorOperator_inner_single]
  simp only [Prod.mk.injEq]

theorem hardyPGram_fourier_neg_nat (i j : Fin r) (n : ℕ) :
    fourierCoeff (hardyWeightedPoint L
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i)
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j)) (-(n : ℤ)) =
      if n = 0 ∧ i = j then 1 else 0 := by
  rw [← hardyWeightedInner_shift_right_fourier L hLp, hardyPColumns_shift]
  rw [hardyPColumns, hardyConst_single, hardyFactorOperator_inner_single]
  simp only [Prod.mk.injEq, eq_comm]

theorem hardyPGram_fourier (i j : Fin r) (n : ℤ) :
    fourierCoeff (hardyWeightedPoint L
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i)
      (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j)) n =
      if n = 0 then (1 : Matrix (Fin r) (Fin r) ℂ) i j else 0 := by
  cases n with
  | ofNat n =>
    calc
      _ = if n = 0 ∧ i = j then 1 else 0 :=
        hardyPGram_fourier_nat L hLp hHerm m hm hLower M hM hUpper i j n
      _ = _ := by
        by_cases hn : n = 0 <;> by_cases hij : i = j <;> simp [hn, hij, Matrix.one_apply]
  | negSucc n =>
    have h := hardyPGram_fourier_neg_nat L hLp hHerm m hm hLower M hM hUpper i j (n + 1)
    have hc : fourierCoeff (hardyWeightedPoint L
        (hardyPColumns L hLp hHerm m hm hLower M hM hUpper i)
        (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j)) (Int.negSucc n) = 0 := by
      simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, false_and, ite_false,
        Int.natCast_add, Int.natCast_one, Int.negSucc_eq] using h
    exact hc.trans (if_neg (Int.negSucc_ne_zero n)).symm

end Yau.NodeProofs.D06Aux
