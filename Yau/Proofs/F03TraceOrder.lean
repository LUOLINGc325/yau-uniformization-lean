import Yau.Proofs.G04Whitening
import Yau.Proofs.G04SpectralBounds
import Yau.Blueprint.Stages

/-! A positive tensor is dominated by its actual relative trace in the reference metric. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint NodeProofs.G04Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem posSemidef_le_relative_trace_bound
    (H G : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hG : G.PosSemidef)
    {C : ℝ} (hC : 0 ≤ C) (hTrace : traceWith H G ≤ C) :
    HermLE G ((C : ℂ) • H) := by
  obtain ⟨S,hS,hu,hsq,hSHS⟩ := exists_hermitian_whitening H hH
  let Q := S*G*S
  have hQ : Q.PosSemidef := by
    simpa only [Q,hS.eq] using hG.conjTranspose_mul_mul_same S
  have hTraceQ : (Matrix.trace Q).re ≤ C := by
    change (Matrix.trace (S*G*S)).re ≤ C
    rw [whitening_trace H G S hsq]
    exact hTrace
  rw [hQ.1.trace_eq_sum_eigenvalues] at hTraceQ
  simp only [Complex.re_sum,Complex.ofReal_re] at hTraceQ
  have hEigen : ∀ i,-C ≤ hQ.1.eigenvalues i ∧ hQ.1.eigenvalues i ≤ C := by
    intro i
    have hi0 := hQ.eigenvalues_nonneg i
    have hi : hQ.1.eigenvalues i ≤ ∑ j,hQ.1.eigenvalues j :=
      Finset.single_le_sum (fun j _ => hQ.eigenvalues_nonneg j) (Finset.mem_univ i)
    exact ⟨by linarith,hi.trans hTraceQ⟩
  have hOrderQ := (hermitian_order_eigenvalues Q hQ.1 C).mpr hEigen
  exact ((whitening_order_iff H G S hS hu hSHS C).mpr hOrderQ).2

end Yau.Proofs.F03Aux
