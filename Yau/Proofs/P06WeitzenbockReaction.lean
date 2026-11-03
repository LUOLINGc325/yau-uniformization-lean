import Yau.Proofs.P06Weitzenbock

/-! Finite curvature reaction and energy identities, with their exact clock. -/

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.P06Weitzenbock

section Finite
variable {ι : Type*} [Fintype ι]

/-- Diagonal of the Hodge curvature action in a unitary eigenbasis. -/
def diagonalReaction (r : ι → ι → ℝ) (eig : ι → ℝ) (i : ι) : ℝ :=
  2 * ∑ j, r i j * (eig i - eig j)

/-- Curvature energy, with the actual Hodge normalization. -/
def diagonalCurvatureEnergy (r : ι → ι → ℝ) (eig : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, r i j * (eig i - eig j) ^ 2

theorem diagonalReaction_pairing (r : ι → ι → ℝ) (hr : ∀ i j, r i j = r j i)
    (eig : ι → ℝ) :
    (∑ i, diagonalReaction r eig i * eig i) = diagonalCurvatureEnergy r eig := by
  let S := ∑ i, ∑ j, r i j * eig i * (eig i - eig j)
  let T := ∑ i, ∑ j, r i j * eig j * (eig j - eig i)
  have hST : S = T := by
    dsimp [S, T]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hr j i]
  calc
    _ = 2 * S := by
      simp only [diagonalReaction, S, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = S + T := by rw [← hST]; ring
    _ = diagonalCurvatureEnergy r eig := by
      simp only [S, T, diagonalCurvatureEnergy, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem diagonalReaction_trace (r : ι → ι → ℝ) (hr : ∀ i j, r i j = r j i)
    (eig : ι → ℝ) : (∑ i, diagonalReaction r eig i) = 0 := by
  have he : (∑ i, ∑ j, r i j * (eig i - eig j)) =
      -(∑ i, ∑ j, r i j * (eig i - eig j)) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hr j i]
    ring
  simp only [diagonalReaction, ← Finset.mul_sum]
  linarith

theorem diagonalCurvatureEnergy_nonneg (r : ι → ι → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) (eig : ι → ℝ) :
    0 ≤ diagonalCurvatureEnergy r eig :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => mul_nonneg (hr i j) (sq_nonneg _)))

/-- The reaction of the paper's generator is minus one half of Q. -/
theorem normalizedReaction_at_null (r : ι → ι → ℝ) (eig : ι → ℝ)
    (i : ι) (hi : eig i = 0) :
    -diagonalReaction r eig i / 2 = ∑ j, r i j * eig j := by
  simp only [diagonalReaction, hi, zero_sub, mul_neg, Finset.sum_neg_distrib]
  ring

theorem normalizedReaction_at_null_nonneg (r : ι → ι → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) (eig : ι → ℝ) (heig : ∀ j, 0 ≤ eig j)
    (i : ι) (hi : eig i = 0) : 0 ≤ -diagonalReaction r eig i / 2 := by
  rw [normalizedReaction_at_null r eig i hi]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hr i j) (heig j))

/-- Any scalar contraction decreases the curvature energy. No derivative,
spectral simplicity, curvature size bound or dimension bound is needed. -/
theorem diagonalCurvatureEnergy_contraction (r : ι → ι → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) (eig : ι → ℝ) (f : ℝ → ℝ)
    (hf : ∀ i j, |f (eig i) - f (eig j)| ≤ |eig i - eig j|) :
    diagonalCurvatureEnergy r (f ∘ eig) ≤ diagonalCurvatureEnergy r eig := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (sq_le_sq.mpr (hf i j)) (hr i j)

end Finite

section ComplexFinite
variable {n : ℕ}

def finiteRicci (R : Fin n → Fin n → Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => ∑ k, R b a k k

def finiteCurvatureAction (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => ∑ k, ∑ l, R b a k l * A k l

def finiteHermitianReaction (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  finiteRicci R * A + A * finiteRicci R - (2 : ℂ) • finiteCurvatureAction R A

theorem sum_four_blocks {α : Type*} [AddCommMonoid α]
    (F : Fin n → Fin n → Fin n → Fin n → α) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext k
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext k
    rw [Finset.sum_comm]

theorem finiteCurvatureAction_trace_selfadjoint
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, R i j k l = R k l i j)
    (B D : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (B * finiteCurvatureAction R D) =
      Matrix.trace (D * finiteCurvatureAction R B) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, finiteCurvatureAction,
    Finset.mul_sum]
  rw [sum_four_blocks]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hR i j k l]
  ring

theorem finiteHermitianReaction_diagonal (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (eig : Fin n → ℝ) (i : Fin n) :
    finiteHermitianReaction R (Matrix.diagonal (fun j => (eig j : ℂ))) i i =
      2 * ∑ j, R i i j j * ((eig i - eig j : ℝ) : ℂ) := by
  have hC : finiteCurvatureAction R (Matrix.diagonal (fun j => (eig j : ℂ))) i i =
      ∑ j, R i i j j * (eig j : ℂ) := by
    simp [finiteCurvatureAction, Matrix.diagonal_apply, mul_ite]
  simp only [finiteHermitianReaction, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul,
    hC, finiteRicci, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  have he : (∑ j, R i i j j * (eig i : ℂ)) = ∑ j, (eig i : ℂ) * R i i j j := by
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [he]
  simp only [← Finset.mul_sum]
  have hf : (eig i : ℂ) * (∑ j, R i i j j) = ∑ j, (eig i : ℂ) * R i i j j :=
    Finset.mul_sum _ _ _
  simp only [hf]
  ring

theorem finiteHermitianReaction_diagonal_re (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (eig : Fin n → ℝ) (i : Fin n) :
    (finiteHermitianReaction R (Matrix.diagonal (fun j => (eig j : ℂ))) i i).re =
      diagonalReaction (fun a b => (R a a b b).re) eig i := by
  rw [finiteHermitianReaction_diagonal]
  simp [diagonalReaction, Complex.mul_re, Complex.ofReal_sub]

theorem finiteHermitianReaction_energy (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j, R i i j j = R j j i i) (eig : Fin n → ℝ) :
    (Matrix.trace (finiteHermitianReaction R (Matrix.diagonal (fun j => (eig j : ℂ))) *
      Matrix.diagonal (fun j => (eig j : ℂ)))).re =
      diagonalCurvatureEnergy (fun a b => (R a a b b).re) eig := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, finiteHermitianReaction_diagonal_re]
  exact diagonalReaction_pairing _ (fun i j => congrArg Complex.re (hR i j)) eig

end ComplexFinite
end Yau.NodeProofs.P06Weitzenbock
