import Yau.Proofs.V03LeviChain

/-! Hermitian symmetry and entrywise smoothness of the actual real-function
Levi matrices, obtained from the real second Fréchet derivative. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedWirt_real_conj {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    star (wirt (fun y => wirtBar (fun x => (f x : ℂ)) y v) z w) =
      wirt (fun y => wirtBar (fun x => (f x : ℂ)) y w) z v := by
  have hF : ContDiffAt ℝ 2 (fun x => (f x : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hd := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [mixedWirt_eq_secondFDeriv hd, mixedWirt_eq_secondFDeriv hd]
  simp only [secondFDeriv_ofReal hf]
  have hsym := hf.isSymmSndFDerivAt (by norm_num)
  have h1 := hsym v w
  have h2 := hsym (Complex.I • v) (Complex.I • w)
  have h3 := hsym v (Complex.I • w)
  have h4 := hsym (Complex.I • v) w
  apply Complex.ext <;>
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, add_zero, zero_add, sub_zero] <;> norm_num <;> linarith

theorem leviMatrix_isHermitian {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (dir : ι → E) : (leviMatrix f z dir).IsHermitian := by
  ext a b
  exact mixedWirt_real_conj hf (dir b) (dir a)

theorem mixedWirt_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (v w : E) :
    ContDiffOn ℝ ∞ (fun z => wirt (fun y => wirtBar f y v) z w) U := by
  have hH := (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU
    (m := ∞) (by simp)
  have h1 := (hH.clm_apply (contDiffOn_const (c := w))).clm_apply
    (contDiffOn_const (c := v))
  have h2 := (hH.clm_apply (contDiffOn_const (c := Complex.I • w))).clm_apply
    (contDiffOn_const (c := Complex.I • v))
  have h3 := (hH.clm_apply (contDiffOn_const (c := w))).clm_apply
    (contDiffOn_const (c := Complex.I • v))
  have h4 := (hH.clm_apply (contDiffOn_const (c := Complex.I • w))).clm_apply
    (contDiffOn_const (c := v))
  have hh := (contDiffOn_const (c := (1 / 4 : ℂ))).mul
    ((h1.add h2).add ((contDiffOn_const (c := Complex.I)).mul (h3.sub h4)))
  apply hh.congr
  intro z hz
  exact (mixedWirt_eq_secondFDeriv
    (((hf z hz).contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by simp)
      |>.differentiableAt one_ne_zero) v w)

theorem leviMatrix_entry_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (dir : ι → E) (a b : ι) :
    ContDiffOn ℝ ∞ (fun z => leviMatrix f z dir a b) U :=
  mixedWirt_contDiffOn hU (Complex.ofRealCLM.contDiff.comp_contDiffOn hf) (dir a) (dir b)

end Yau.Blueprint.V03Proof
