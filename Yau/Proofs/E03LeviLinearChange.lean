import Yau.Proofs.E03JointCoordinates
import Yau.LeafProofs.L18

/-! Real-Hessian transport through the genuine complex-linear joint coordinates. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

theorem secondFDeriv_comp_continuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E →L[ℝ] F) {f : F → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f (e p)) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) p v w =
      fderiv ℝ (fderiv ℝ f) (e p) (e v) (e w) := by
  have he : fderiv ℝ (e : E → F) = fun _ => e := funext (fun x => e.fderiv)
  rw [Yau.LeafProofs.L18Aux.secondFDeriv_comp e.contDiff.contDiffAt hf, he]
  simp

theorem leviMatrix_comp_complexLinearEquiv
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) {f : F → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f (e p))
    (dir : ι → E) :
    leviMatrix (f ∘ e) p dir = leviMatrix f (e p) (fun i => e (dir i)) := by
  have he : ContDiffAt ℝ 2 (e : E → F) p := e.toContinuousLinearMap.contDiff.restrict_scalars ℝ |>.contDiffAt
  have hcomp : ContDiffAt ℝ 2 (f ∘ e) p := hf.comp p he
  have hchain (v w : E) : fderiv ℝ (fderiv ℝ (f ∘ e)) p v w =
      fderiv ℝ (fderiv ℝ f) (e p) (e v) (e w) :=
    secondFDeriv_comp_continuousLinearMap (e.toContinuousLinearMap.restrictScalars ℝ) hf v w
  ext i j
  apply Complex.ext
  · simp only [(Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hcomp dir i j).1,
      (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf (fun i => e (dir i)) i j).1,
      hchain, map_smul]
  · simp only [(Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hcomp dir i j).2,
      (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf (fun i => e (dir i)) i j).2,
      hchain, map_smul]

theorem jointLevi_eq_submatrix {n : ℕ} {F : JointSpace n → ℝ} {p : JointSpace n}
    (hF : ContDiffAt ℝ 2 F p) :
    leviMatrix F p jointDir =
      (leviC (F ∘ jointContinuousLinearEquiv n) ((jointContinuousLinearEquiv n).symm p)).submatrix
        (Fintype.equivFin (JointIndex n)) (Fintype.equivFin (JointIndex n)) := by
  let e := jointContinuousLinearEquiv n
  have hh := leviMatrix_comp_complexLinearEquiv e
    (p := e.symm p) (by simpa only [e.apply_symm_apply] using hF)
    (fun i : JointIndex n => stdVec (Fintype.equivFin (JointIndex n) i))
  ext i j
  have hij := congrFun (congrFun hh.symm i) j
  simpa only [leviC, leviMatrix, Matrix.submatrix_apply, e, ContinuousLinearEquiv.apply_symm_apply,
    jointContinuousLinearEquiv_stdVec] using hij

end Yau.NodeProofs.E03Aux
