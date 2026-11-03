import Yau.Blueprint.Nodes

open Matrix
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The positive determinant and real trace are the actual spectral
product and sum. The choice of eigenbasis is pointwise only. -/
theorem posDef_spectral_det_trace {n : ℕ} (A : Herm n) (hA : A.PosDef) :
    A.det.re = ∏ i, hA.isHermitian.eigenvalues i ∧
    (Matrix.trace A).re = ∑ i, hA.isHermitian.eigenvalues i := by
  constructor
  · rw [hA.isHermitian.det_eq_prod_eigenvalues,←RCLike.ofReal_prod]
    rfl
  · rw [hA.isHermitian.trace_eq_sum_eigenvalues,←RCLike.ofReal_sum]
    rfl

theorem posDef_logdet_eq_sum_log_eigenvalues {n : ℕ} (A : Herm n) (hA : A.PosDef) :
    Real.log A.det.re = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
  rw [(posDef_spectral_det_trace A hA).1]
  exact Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')

/-- The spectral logdet support inequality, including dimension zero. -/
theorem logdet_le_trace_sub_dim {n : ℕ} (A : Herm n) (hA : A.PosDef) :
    (n:ℝ)+Real.log A.det.re ≤ (Matrix.trace A).re := by
  have hSum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  have hTrace := (posDef_spectral_det_trace A hA).2
  have hLog := posDef_logdet_eq_sum_log_eigenvalues A hA
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one] at hSum
  linarith

/-- Equality in the spectral support inequality forces every eigenvalue
to be one and hence the original matrix itself to be the identity. -/
theorem logdet_eq_trace_sub_dim_iff {n : ℕ} (A : Herm n) (hA : A.PosDef) :
    ((n:ℝ)+Real.log A.det.re = (Matrix.trace A).re) ↔ A = 1 := by
  constructor
  · intro hEq
    let eig := hA.isHermitian.eigenvalues
    have hNonneg : ∀ i : Fin n, 0 ≤ eig i-1-Real.log (eig i) := by
      intro i
      exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
    have hTrace := (posDef_spectral_det_trace A hA).2
    have hLog := posDef_logdet_eq_sum_log_eigenvalues A hA
    have hSum : ∑ i, (eig i-1-Real.log (eig i)) = 0 := by
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,mul_one]
      change (∑ i, hA.isHermitian.eigenvalues i)-(n:ℝ)-
        (∑ i, Real.log (hA.isHermitian.eigenvalues i)) = 0
      linarith
    have hEach : ∀ i : Fin n, hA.isHermitian.eigenvalues i = 1 := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hNonneg j)).mp hSum i (Finset.mem_univ i)
      by_contra hNe
      have hLt := Real.log_lt_sub_one_of_pos (hA.eigenvalues_pos i) hNe
      change eig i ≠ 1 at hNe
      change Real.log (eig i) < eig i-1 at hLt
      linarith
    have hDiag : Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) = (1 : Herm n) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Function.comp_apply,hEach]
      · simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
    rw [hA.isHermitian.spectral_theorem,hDiag,map_one]
  · rintro rfl
    simp

end Yau.NodeProofs.E02Aux
