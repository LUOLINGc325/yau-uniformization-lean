import Yau.Proofs.C03LogDualBasic
import Yau.LeafProofs.L22LeviBasic

/-! Restrict the already proved product calculator to the genuine constant-fiber graph. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Set Filter
namespace Yau.Proofs.C03Aux.LogDual
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.Blueprint.V03Proof Yau.LeafProofs L22Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem secondFDeriv_const_fiber {F : CotangentCoord n → ℝ}
    {z xi : ComplexVector n} (hF : ContDiffAt ℝ 2 F (z, xi))
    (a b : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun w => F (w, xi))) z a b =
      fderiv ℝ (fderiv ℝ F) (z, xi) (a, 0) (b, 0) := by
  let T : ComplexVector n → CotangentCoord n := fun w => (w, xi)
  let L : ComplexVector n →L[ℝ] CotangentCoord n := (ContinuousLinearMap.id ℝ _).prod 0
  have hTd (y : ComplexVector n) : HasFDerivAt T L y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const xi y)
  have hder : fderiv ℝ T = fun _ => L := funext (fun y => (hTd y).fderiv)
  have hzero : fderiv ℝ (fun _ : ComplexVector n => L) z = 0 := fderiv_const_apply L
  have hT : ContDiffAt ℝ 2 T z := contDiffAt_id.prodMk contDiffAt_const
  have hh := L18Aux.secondFDeriv_comp hT hF a b
  simpa only [Function.comp_def, hder, hzero, ContinuousLinearMap.zero_apply,
    map_zero, add_zero, T, L, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply] using hh

theorem dualSquared_levi_completion {U : Set (ComplexVector n)} (hU : IsOpen U)
    (H : ComplexVector n → Herm n) (hHerm : ∀ z, (H z).IsHermitian)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef)
    (z : ComplexVector n) (hz : z ∈ U) (xi a : ComplexVector n) :
    complexLeviQuadratic (dualSquared H xi) z a =
      ellipsoidQuadratic ((H z)⁻¹)ᵀ (connectionVector H z xi a) +
        computedResidual H z xi a := by
  let F : CotangentCoord n → ℝ := fun p => dualNormMat (H p.1) p.2
  have hF : ContDiffAt ℝ 2 F (z, xi) :=
    ((dualNormMat_product_contDiffOn H hH hPos).contDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)).of_le (by simp)
  have hm := dualNormMat_product_mixed hU H hHerm hH
    (fun w hw => (hPos w hw).det_pos.ne') z hz xi a 0
  have hdiag := (L18Aux.leviMatrix_entry_re_im hF (fun _ : Fin 1 => (a, 0)) 0 0).1
  change (wirt (fun p => wirtBar (fun q : CotangentCoord n => (F q : ℂ))
    p (a, 0)) (z, xi) (a, 0)).re = _ at hdiag
  have hIa : Complex.I • (a, (0 : ComplexVector n)) = (Complex.I • a, 0) := by simp
  rw [hdiag, hIa] at hm
  have ha := secondFDeriv_const_fiber hF a a
  have hia := secondFDeriv_const_fiber hF (Complex.I • a) (Complex.I • a)
  change (1 / 4 : ℝ) * _ = _ at hm
  change (fderiv ℝ (fderiv ℝ (fun w => F (w, xi))) z a a +
    fderiv ℝ (fderiv ℝ (fun w => F (w, xi))) z (Complex.I • a) (Complex.I • a)) / 4 = _
  rw [ha, hia]
  simpa only [zero_sub, connectionVector, computedResidual, F, div_eq_mul_inv, one_mul, mul_comm] using hm

end Yau.Proofs.C03Aux.LogDual

