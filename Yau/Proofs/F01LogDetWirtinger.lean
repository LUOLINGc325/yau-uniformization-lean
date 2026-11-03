import Yau.Proofs.F01LogDetDifferential
import Yau.Proofs.F01ConformalGradient
import Yau.Proofs.F01KahlerMixedExchange

/-! The actual unbarred log-determinant derivative is the original complex
inverse trace; positivity makes the real determinant coercion legitimate. -/
noncomputable section
open Set Filter
open scoped Matrix ComplexOrder Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem logdet_wirt_trace (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} (hS : IsOpen S) {z : ComplexVector n}
    (hz : z ∈ S) (v : ComplexVector n)
    (hH : DifferentiableAt ℝ H z) (hpos : ∀ w ∈ S, (H w).PosDef) :
    wirt (fun w => (Real.log (H w).det.re : ℂ)) z v =
      Matrix.trace ((H z)⁻¹ * Matrix.of (fun i j => wirt (fun w => H w i j) z v)) := by
  have hd := L07Aux.matrix_determinant_differentiableAt H z hH
  have hdr : DifferentiableAt ℝ (fun w => (H w).det.re) z :=
    Complex.reCLM.differentiableAt.comp z hd
  have hp := Complex.pos_iff.mp (hpos z hz).det_pos
  have hgerm : (fun w => ((H w).det.re : ℂ)) =ᶠ[𝓝 z] (fun w => (H w).det) := by
    filter_upwards [hS.mem_nhds hz] with w hw
    apply Complex.ext
    · rfl
    · exact (Complex.pos_iff.mp (hpos w hw).det_pos).2
  have hcx : (((H z).det.re : ℝ) : ℂ) = (H z).det := hgerm.eq_of_nhds
  have hc : (((H z).det.re⁻¹ : ℝ) : ℂ) * (H z).det = 1 := by
    calc
      (((H z).det.re⁻¹ : ℝ) : ℂ) * (H z).det =
          (((H z).det.re⁻¹ : ℝ) : ℂ) * (((H z).det.re : ℝ) : ℂ) :=
        congrArg (fun D : ℂ => (((H z).det.re⁻¹ : ℝ) : ℂ) * D) hcx.symm
      _ = 1 := by rw [← Complex.ofReal_mul, inv_mul_cancel₀ hp.1.ne', Complex.ofReal_one]
  rw [wirt_ofReal_scalar_comp hdr (Real.hasDerivAt_log hp.1.ne') v,
    wirt_eq_of_eventuallyEq hgerm, L07Aux.determinant_wirt H z v hH
      ((hpos z hz).isUnit.map Matrix.detMonoidHom), ← mul_assoc, hc, one_mul]

end Yau.NodeProofs.F01Aux
