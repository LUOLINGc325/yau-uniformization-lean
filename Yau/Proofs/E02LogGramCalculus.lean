import Yau.Proofs.E02GramSmooth

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def logGram {n m : ℕ} (M : Rect n m) : ℝ := Real.log (M*Mᴴ).det.re

theorem logGram_contDiffOn (n m : ℕ) : ContDiffOn ℝ ∞ (logGram (n := n) (m := m)) (fullRankRect n m) := by
  have hd : ContDiffOn ℝ ∞ (fun M : Rect n m => (M*Mᴴ).det) (fullRankRect n m) :=
    Yau.LeafProofs.L07Aux.matrix_determinant_contDiffOn
    (fun M : Rect n m => M*Mᴴ) (gram_contDiff n m).contDiffOn
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hd
  exact hr.log fun M hM =>
    (RCLike.pos_iff.mp ((fullRankRect_iff_posDef M).mp hM).det_pos).1.ne'

/-- The genuine first real derivative of the rectangular Gram logdet. -/
theorem logGram_fderiv_apply {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    fderiv ℝ logGram M Z = (Matrix.trace ((M*Mᴴ)⁻¹*(M*Zᴴ+Z*Mᴴ))).re := by
  have hG := (gram_hasFDerivAt M).differentiableAt
  have hd := Yau.LeafProofs.L07Aux.matrix_determinant_differentiableAt
    (fun N : Rect n m => N*Nᴴ) M hG
  have hRe : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ).det.re) M :=
    Complex.reCLM.differentiableAt.comp M hd
  have hPos : 0 < (M*Mᴴ).det.re := (RCLike.pos_iff.mp hM.det_pos).1
  have hIm : (M*Mᴴ).det.im = 0 := (RCLike.pos_iff.mp hM.det_pos).2
  have hdRe : fderiv ℝ (fun N : Rect n m => (N*Nᴴ).det.re) M Z =
      (fderiv ℝ (fun N : Rect n m => (N*Nᴴ).det) M Z).re := by
    have hReal : HasFDerivAt (fun N : Rect n m => (N*Nᴴ).det.re)
        (Complex.reCLM.comp (fderiv ℝ (fun N : Rect n m => (N*Nᴴ).det) M)) M :=
      Complex.reCLM.hasFDerivAt.comp M hd.hasFDerivAt
    exact congrArg (fun L : Rect n m →L[ℝ] ℝ => L Z) hReal.fderiv
  have hdFormula := Yau.LeafProofs.L07Aux.determinant_fderiv_trace
    (fun N : Rect n m => N*Nᴴ) M Z hG (hM.isUnit.map Matrix.detMonoidHom)
  have hLog := hRe.hasFDerivAt.log hPos.ne'
  have hValue := congrArg (fun L : Rect n m →L[ℝ] ℝ => L Z) hLog.fderiv
  change fderiv ℝ logGram M Z =
    (M*Mᴴ).det.re⁻¹*fderiv ℝ (fun N : Rect n m => (N*Nᴴ).det.re) M Z at hValue
  rw [hdRe] at hValue
  erw [hdFormula] at hValue
  rw [Complex.mul_re,hIm,zero_mul,sub_zero] at hValue
  have hGram := congrArg (fun D : Rect n m →L[ℝ] Herm n => D Z) (gram_fderiv M)
  change fderiv ℝ (fun N : Rect n m => N*Nᴴ) M Z = M*Zᴴ+Z*Mᴴ at hGram
  erw [hGram] at hValue
  rw [←mul_assoc,inv_mul_cancel₀ hPos.ne',one_mul] at hValue
  exact hValue

end Yau.NodeProofs.E02Aux
