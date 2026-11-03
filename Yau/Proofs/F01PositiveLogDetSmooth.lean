import Yau.Proofs.F01ScalarSymbolSmooth

/-! The actual positive determinant logarithm is smooth for a genuinely
smooth Frobenius matrix field, with its original real determinant coercion. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_frobenius_logdet_contDiffOn {H : E → Matrix (Fin n) (Fin n) ℂ} {S : Set E}
    (hH : ContDiffOn ℝ ∞ H S) (hpos : ∀ x ∈ S, (H x).PosDef) :
    ContDiffOn ℝ ∞ (fun x => Real.log (H x).det.re) S := by
  have hd := (frobenius_matrix_det_contDiff (n := n)).comp_contDiffOn hH
  have hre : ContDiffOn ℝ ∞ (fun x => (H x).det.re) S := by
    convert! Complex.reCLM.contDiff.comp_contDiffOn hd using 1
  exact hre.log (fun x hx => (Complex.pos_iff.mp (hpos x hx).det_pos).1.ne')

end Yau.NodeProofs.F01Aux
