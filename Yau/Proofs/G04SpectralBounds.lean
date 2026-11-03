import Yau.Proofs.G04FormInnerMatrix
import Mathlib.Analysis.Matrix.Order

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.NodeProofs.G04Aux
open Yau Matrix
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem trace_unitary_conj (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Unitary.conjStarAlgAut ℂ _ U A) = Matrix.trace A := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]

theorem hermitian_square_trace (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q.IsHermitian) :
    (Matrix.trace (Q ^ 2)).re = ∑ i, (hQ.eigenvalues i) ^ 2 := by
  calc
    (Matrix.trace (Q ^ 2)).re = (Matrix.trace
      (Unitary.conjStarAlgAut ℂ _ hQ.eigenvectorUnitary
        ((Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ))) ^ 2))).re := by
      have hspect : Q = Unitary.conjStarAlgAut ℂ _ hQ.eigenvectorUnitary
          (Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ))) := hQ.spectral_theorem
      rw [map_pow, ← hspect]
    _ = _ := by
      rw [trace_unitary_conj]
      simp [pow_two, Matrix.diagonal_mul_diagonal, Complex.re_sum]

theorem hermitian_order_eigenvalues (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q.IsHermitian) (C : ℝ) :
    ((Q - (-C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Q).PosSemidef) ↔
      ∀ i, -C ≤ hQ.eigenvalues i ∧ hQ.eigenvalues i ≤ C := by
  let U := hQ.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) (star U)
  have hu : IsUnit (U : Matrix (Fin n) (Fin n) ℂ) := Unitary.isUnit_coe
  have hφ (A : Matrix (Fin n) (Fin n) ℂ) : (φ A).PosSemidef ↔ A.PosSemidef := by
    simpa only [φ, Unitary.conjStarAlgAut_star_apply] using
      hu.posSemidef_star_left_conjugate_iff (x := A)
  have hdiag : φ Q = Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ)) :=
    hQ.conjStarAlgAut_star_eigenvectorUnitary
  have h₁ := hφ (Q - (-C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
  have h₂ := hφ ((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Q)
  rw [map_sub, map_smul, map_one, hdiag] at h₁ h₂
  have hD₁ : Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ)) - (-C : ℂ) •
      (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ) - (-C : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  have hD₂ : (C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ)) = Matrix.diagonal (fun i => (C : ℂ) - hQ.eigenvalues i) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  rw [hD₁, Matrix.posSemidef_diagonal_iff] at h₁
  rw [hD₂, Matrix.posSemidef_diagonal_iff] at h₂
  rw [← h₁, ← h₂]
  simp only [Complex.nonneg_iff, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    neg_zero, sub_zero, sub_self, and_true]
  constructor
  · intro h i
    constructor <;> linarith [h.1 i, h.2 i]
  · intro h
    exact ⟨fun i => by linarith [(h i).1], fun i => by linarith [(h i).2]⟩

theorem hermitian_order_of_square_trace (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) {C : ℝ} (hC : 0 ≤ C) (hb : (Matrix.trace (Q ^ 2)).re ≤ C ^ 2) :
    (Q - (-C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Q).PosSemidef := by
  apply (hermitian_order_eigenvalues Q hQ C).mpr
  intro i
  have hi : (hQ.eigenvalues i) ^ 2 ≤ ∑ j, (hQ.eigenvalues j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [hermitian_square_trace Q hQ] at hb
  constructor <;> nlinarith

theorem hermitian_square_trace_of_order (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) {C : ℝ} (hC : 0 ≤ C)
    (hb : (Q - (-C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Q).PosSemidef) :
    (Matrix.trace (Q ^ 2)).re ≤ (n : ℝ) * C ^ 2 := by
  rw [hermitian_square_trace Q hQ]
  have hi := (hermitian_order_eigenvalues Q hQ C).mp hb
  calc
    (∑ i, (hQ.eigenvalues i) ^ 2) ≤ ∑ _ : Fin n, C ^ 2 :=
      Finset.sum_le_sum (fun i _ => by nlinarith [(hi i).1, (hi i).2])
    _ = _ := by simp

theorem hermitian_trace_of_order (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) {C : ℝ} (hC : 0 ≤ C)
    (hb : (Q - (-C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Q).PosSemidef) :
    |(Matrix.trace Q).re| ≤ (n : ℝ) * C := by
  have hi := (hermitian_order_eigenvalues Q hQ C).mp hb
  rw [hQ.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re]
  calc
    |∑ i, hQ.eigenvalues i| ≤ ∑ i, |hQ.eigenvalues i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, C := Finset.sum_le_sum (fun i _ => abs_le.mpr (hi i))
    _ = _ := by simp

end Yau.NodeProofs.G04Aux
