import Yau.Proofs.G04Whitening
import Yau.Proofs.G04SpectralBounds
import Yau.Blueprint.Stages

/-! A relative upper Hessian estimate and a lower trace estimate give the
needed lower Hessian estimate in the original Hermitian metric. -/
noncomputable section
open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem posSemidef_le_trace_identity (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q.PosSemidef) :
    (((Matrix.trace Q).re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Q).PosSemidef := by
  have ht : (Matrix.trace Q).re = ∑ i, hQ.1.eigenvalues i := by
    rw [hQ.1.trace_eq_sum_eigenvalues]
    simp
  have htr : 0 ≤ (Matrix.trace Q).re := by
    rw [ht]
    exact Finset.sum_nonneg (fun i _ => hQ.eigenvalues_nonneg i)
  apply ((G04Aux.hermitian_order_eigenvalues Q hQ.1 (Matrix.trace Q).re).mpr ?_).2
  intro i
  refine ⟨by linarith [hQ.eigenvalues_nonneg i], ?_⟩
  rw [ht]
  exact Finset.single_le_sum (fun j _ => hQ.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem posSemidef_le_scalar_of_trace_le (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.PosSemidef) {B : ℝ} (hb : (Matrix.trace Q).re ≤ B) :
    ((B : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Q).PosSemidef := by
  have hp := (posSemidef_le_trace_identity Q hQ).add
    ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosSemidef).smul
      (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hb, rfl⟩ : 0 ≤ ((B - (Matrix.trace Q).re : ℝ) : ℂ)))
  convert hp using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_sub]
  ring

theorem relative_lower_bound_of_upper_and_trace
    (H B : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) {a b : ℝ} (ha : 0 ≤ a)
    (hupper : HermLE B ((a : ℂ) • H)) (htrace : -b ≤ traceWith H B) :
    HermLE ((-((n : ℝ) * a + b) : ℂ) • H) B := by
  obtain ⟨S, hS, hu, hSS, hSHS⟩ := G04Aux.exists_hermitian_whitening H hH
  let Q := S * ((a : ℂ) • H - B) * S
  have hQ : Q.PosSemidef := by
    have hp := hupper.conjTranspose_mul_mul_same S
    simpa only [hS.eq] using hp
  have hQexpr : Q = (a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - S * B * S := by
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hSHS]
  have hQtrace : (Matrix.trace Q).re = (n : ℝ) * a - traceWith H B := by
    rw [hQexpr, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Complex.sub_re,
      G04Aux.whitening_trace H B S hSS]
    simp [smul_eq_mul]
    ring
  have hbound := posSemidef_le_scalar_of_trace_le Q hQ
    (show (Matrix.trace Q).re ≤ (n : ℝ) * a + b by rw [hQtrace]; linarith)
  have haI : ((a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (Complex.nonneg_iff.mpr ⟨ha, rfl⟩)
  apply (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hu (x := B - (-((n : ℝ) * a + b) : ℂ) • H)).mp
  rw [hS.star_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hSHS]
  have hp := hbound.add haI
  rw [hQexpr] at hp
  convert hp using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_mul]
  ring

end Yau.NodeProofs.P07Aux
