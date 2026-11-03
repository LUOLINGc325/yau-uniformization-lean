import Yau.Proofs.F01PotentialSpatialLinearization

/-! The spatial differential of the actual nonlinear log determinant
uses only the genuine smooth spatial slice. This separates the algebraic
linearization from any assertion of joint smoothness across time zero. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def spatialPotentialMatrix (A : Space n → Matrix (Fin n) (Fin n) ℂ)
    (q : Space n → ℝ) (z : Space n) : Matrix (Fin n) (Fin n) ℂ := A z + leviC q z

theorem potential_log_spatial_derivative
    (A : Space n → Matrix (Fin n) (Fin n) ℂ) (q b : Space n → ℝ)
    {S : Set (Space n)} (hS : IsOpen S) (hA : ContDiffOn ℝ ∞ A S)
    (hq : ContDiffOn ℝ ∞ q S) (hb : ContDiffOn ℝ ∞ b S)
    (hpos : ∀ z ∈ S, (spatialPotentialMatrix A q z).PosDef)
    {x : Space n} (hx : x ∈ S) (v : Space n) :
    fderiv ℝ (fun z => Real.log (spatialPotentialMatrix A q z).det.re + b z) x v =
      traceWith (spatialPotentialMatrix A q x)
        (leviC (fun z => fderiv ℝ q z v) x) +
      traceWith (spatialPotentialMatrix A q x) (fderiv ℝ A x v) + fderiv ℝ b x v := by
  have hL := native_levi_frobenius_contDiffOn hS hq
  have hH : ContDiffOn ℝ ∞ (spatialPotentialMatrix A q) S := hA.add hL
  have hHd := (hH.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
  have hLog := positive_frobenius_logdet_contDiffOn hH hpos
  have hLogd := (hLog.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
  have hbd := (hb.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
  have hMatrix : fderiv ℝ (spatialPotentialMatrix A q) x v =
      fderiv ℝ A x v + leviC (fun z => fderiv ℝ q z v) x := by
    have hAd := (hA.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
    have hLd := (hL.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
    have hd := hAd.hasFDerivAt.add hLd.hasFDerivAt
    have he := congrArg (fun D : Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ => D v) hd.fderiv
    have hpoint : fderiv ℝ (fun z => A z + leviC q z) x v =
        fderiv ℝ A x v + fderiv ℝ (fun z => leviC q z) x v := by
      convert! he using 1
    exact hpoint.trans (congrArg (fun H : Matrix (Fin n) (Fin n) ℂ => fderiv ℝ A x v + H)
      (leviC_spatial_direction_commute hS hq hx v))
  rw [fderiv_fun_add hLogd hbd]
  simp only [add_apply]
  rw [frobenius_logdet_fderiv_trace _ x v hHd (hpos x hx), hMatrix, traceWith_add]
  ring

end Yau.NodeProofs.F01Aux
