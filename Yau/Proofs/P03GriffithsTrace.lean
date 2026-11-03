import Yau.LeafProofs.L07

open scoped Matrix ComplexOrder
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

theorem griffithsQuadratic_basis (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (ξ : ComplexVector n) (α : Fin r) :
    griffithsQuadratic R ξ (stdVec α) =
      (∑ i, ∑ j, R i j α α * ξ i * star (ξ j)).re := by
  simp [griffithsQuadratic, stdVec, PiLp.single_apply]

theorem griffiths_trace_sum (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (ξ : ComplexVector n) :
    (∑ i, ∑ j, Matrix.trace (R i j) * ξ i * star (ξ j)).re =
      ∑ α, griffithsQuadratic R ξ (stdVec α) := by
  simp only [griffithsQuadratic_basis, Matrix.trace, Matrix.diag_apply, Finset.sum_mul,
    Complex.re_sum]
  calc
    _ = ∑ i, ∑ α, ∑ j, (R i j α α * ξ i * star (ξ j)).re := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Taking the metric trace of a Griffiths nonnegative tensor is nonnegative
on each base direction; no tangent Nakano condition is used. -/
theorem griffiths_metric_trace_nonnegative {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (b : Module.Basis (Fin r) ℂ V)
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (hR : ∀ ξ v, 0 ≤ griffithsQuadratic R ξ v) (ξ : ComplexVector n) :
    0 ≤ (∑ i, ∑ j, Matrix.trace ((hermitianGram h b)⁻¹ * R i j) *
      ξ i * star (ξ j)).re := by
  obtain ⟨c, hc⟩ := L07Aux.hermitian_exists_orthonormal_basis h b
  let T := b.toMatrix c
  have hi : (hermitianGram h b)⁻¹ = T * Tᴴ := L07Aux.hermitianGram_inv_factor h b c hc
  have htr (i j : Fin n) :
      Matrix.trace ((hermitianGram h b)⁻¹ * R i j) = Matrix.trace (Tᴴ * R i j * T) := by
    rw [hi]
    rw [Matrix.mul_assoc]
    exact Matrix.trace_mul_comm T (Tᴴ * R i j)
  simp_rw [htr]
  rw [griffiths_trace_sum]
  apply Finset.sum_nonneg
  intro α _
  rw [L07Aux.griffithsQuadratic_conjugate]
  exact hR _ _

end Yau.NodeProofs.P03Aux
