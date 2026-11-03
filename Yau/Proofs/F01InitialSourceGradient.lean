import Yau.Proofs.F01CompactTaylorHolder
import Yau.Proofs.F01FrobeniusLogDetDifferential
import Yau.Proofs.F01ScalarSymbolSmooth

/-! The entire first differentiated initial forcing is an actual smooth
finite-dimensional function of the positive matrix and the background
first jets. Evaluation in a direction gives its computed inverse trace. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

local instance sourceMatrixDualNormed (n : ℕ) :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance sourceSpatialMatrixNormed (n : ℕ) :
    NormedAddCommGroup (Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance sourceMatrixDualSpace (n : ℕ) :
    NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance sourceSpatialMatrixSpace (n : ℕ) :
    NormedSpace ℝ (Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  ContinuousLinearMap.toNormedSpace

abbrev PotentialSourceInput (n : ℕ) := Matrix (Fin n) (Fin n) ℂ ×
  ((Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) × (Space n →L[ℝ] ℝ))

def potentialSourceGradient (p : PotentialSourceInput n) : Space n →L[ℝ] ℝ :=
  (fderiv ℝ (fun H : Matrix (Fin n) (Fin n) ℂ => Real.log H.det.re) p.1).comp p.2.1 + p.2.2

def potentialSourceDomain (n : ℕ) : Set (PotentialSourceInput n) :=
  {p | p.1.det.re ≠ 0}

theorem real_frobenius_logdet_contDiffOn :
    ContDiffOn ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => Real.log H.det.re)
      {H | H.det.re ≠ 0} := by
  have hd := Complex.reCLM.contDiff.comp (frobenius_matrix_det_contDiff (n := n))
  exact hd.contDiffOn.log (fun H hH => hH)

theorem potentialSourceDomain_isOpen : IsOpen (potentialSourceDomain n) :=
  isOpen_ne_fun (Complex.reCLM.continuous.comp
    (frobenius_matrix_det_contDiff.continuous.comp continuous_fst)) continuous_const

theorem potentialSourceGradient_contDiffOn (n : ℕ) :
    ContDiffOn ℝ ∞ (potentialSourceGradient (n := n)) (potentialSourceDomain n) := by
  have hOpen : IsOpen {H : Matrix (Fin n) (Fin n) ℂ | H.det.re ≠ 0} :=
    isOpen_ne_fun (Complex.reCLM.continuous.comp frobenius_matrix_det_contDiff.continuous)
      continuous_const
  have hD : ContDiffOn ℝ ∞
      (fderiv ℝ (fun H : Matrix (Fin n) (Fin n) ℂ => Real.log H.det.re))
      {H | H.det.re ≠ 0} :=
    (real_frobenius_logdet_contDiffOn (n := n)).fderiv_of_isOpen hOpen (by simp)
  have hA : ContDiffOn ℝ ∞ (fun p : PotentialSourceInput n =>
      fderiv ℝ (fun H : Matrix (Fin n) (Fin n) ℂ => Real.log H.det.re) p.1)
      (potentialSourceDomain n) := hD.comp contDiffOn_fst (fun p hp => hp)
  have hB : ContDiffOn ℝ ∞ (fun p : PotentialSourceInput n => p.2.1)
      (potentialSourceDomain n) := by fun_prop
  have hC : ContDiffOn ℝ ∞ (fun p : PotentialSourceInput n => p.2.2)
      (potentialSourceDomain n) := by fun_prop
  exact (hA.clm_comp hB).add hC

theorem potentialSourceGradient_apply (H : Matrix (Fin n) (Fin n) ℂ)
    (D : Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (b : Space n →L[ℝ] ℝ)
    (hH : H.PosDef) (v : Space n) :
    potentialSourceGradient (H, (D, b)) v = traceWith H (D v) + b v := by
  let I := ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)
  have he := @frobenius_logdet_fderiv_trace n (Matrix (Fin n) (Fin n) ℂ)
    (inferInstance : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ))
    (inferInstance : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ))
    I H (D v) I.differentiableAt hH
  have hI : fderiv ℝ I H = I := I.fderiv
  have heval : fderiv ℝ I H (D v) = D v := by
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ →L[ℝ]
      Matrix (Fin n) (Fin n) ℂ => A (D v)) hI
  change fderiv ℝ (fun w => Real.log w.det.re) H (D v) =
    traceWith H (fderiv ℝ I H (D v)) at he
  rw [heval] at he
  simpa only [potentialSourceGradient, add_apply,
    ContinuousLinearMap.comp_apply, I, ContinuousLinearMap.id_apply] using
    congrArg (fun r : ℝ => r + b v) he

end Yau.NodeProofs.F01Aux
