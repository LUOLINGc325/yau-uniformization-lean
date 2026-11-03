import Yau.Proofs.F01LogDetDifferential

/-! The original determinant trace differential computes the actual
one-sided logarithmic determinant derivative of a matrix curve, entry by entry. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem logdet_curve_hasDerivWithinAt
    (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (Hdot : Matrix (Fin n) (Fin n) ℂ)
    {I : Set ℝ} {t : ℝ} (hH : ∀ i j, HasDerivWithinAt (fun s => H s i j) (Hdot i j) I t)
    (hpos : (H t).PosDef) :
    HasDerivWithinAt (fun s => Real.log (H s).det.re) (traceWith (H t) Hdot) I t := by
  have hmat : HasDerivWithinAt H Hdot I t :=
    hasDerivWithinAt_pi.mpr (fun i => hasDerivWithinAt_pi.mpr (fun j => hH i j))
  let F : Matrix (Fin n) (Fin n) ℂ → ℝ := fun G => Real.log G.det.re
  have hd := Yau.LeafProofs.L07Aux.matrix_determinant_differentiableAt
    (fun G : Matrix (Fin n) (Fin n) ℂ => G) (H t) differentiableAt_id
  have hF : DifferentiableAt ℝ F (H t) :=
    (Complex.reCLM.differentiableAt.comp (H t) hd).log (Complex.pos_iff.mp hpos.det_pos).1.ne'
  have hh := hF.hasFDerivAt.comp_hasDerivWithinAt t hmat
  have hvalue : fderiv ℝ F (H t) Hdot = traceWith (H t) Hdot := by
    change fderiv ℝ (fun G : Matrix (Fin n) (Fin n) ℂ => Real.log G.det.re) (H t) Hdot = _
    convert logdet_fderiv_trace (fun G : Matrix (Fin n) (Fin n) ℂ => G) (H t) Hdot
      differentiableAt_id hpos using 1
    all_goals try rfl
    all_goals erw [fderiv_fun_id, ContinuousLinearMap.id_apply]
  convert hh using 1 <;> first | rfl | exact hvalue.symm | exact hvalue

end Yau.NodeProofs.F01Aux
