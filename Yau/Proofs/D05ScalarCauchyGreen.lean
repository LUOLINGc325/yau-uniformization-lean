import Yau.LeafProofs.L08
import Yau.Proofs.V03LeviChain

/-! The scalar Cauchy–Green operator used in disc trivialization, constructed
from the compact-density Newton potential with its exact normalization. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau Yau.LeafProofs

def compactNewtonPotential (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ w : ℂ, Real.log ‖z - w‖ * f w

def compactDbarRealSolution (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  (2 / Real.pi : ℂ) * wirt (fun w => (compactNewtonPotential f w : ℂ)) z 1

theorem wirtBar_wirt_eq_planarLaplacian {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    wirtBar (fun w => wirt f w 1) z 1 =
      (1 / 4 : ℂ) * LeafCandidates.planarLaplacian f z := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 := hdf.clm_apply (differentiableAt_const (1 : ℂ))
  have hI := hdf.clm_apply (differentiableAt_const Complex.I)
  have hd (v : ℂ) : fderiv ℝ (fun w => wirt f w 1) z v =
      (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) z v 1 -
        Complex.I * fderiv ℝ (fderiv ℝ f) z v Complex.I) := by
    simp only [wirt, smul_eq_mul, mul_one]
    rw [fderiv_const_mul (h1.fun_sub (hI.const_mul Complex.I)),
      fderiv_fun_sub h1 (hI.const_mul Complex.I), fderiv_const_mul hI,
      fderiv_clm_apply hdf (differentiableAt_const (1 : ℂ)),
      fderiv_clm_apply hdf (differentiableAt_const Complex.I)]
    simp
  have hs := hf.isSymmSndFDerivAt (by norm_num) (1 : ℂ) Complex.I
  rw [wirtBar, hd, show Complex.I • (1 : ℂ) = Complex.I by simp, hd]
  unfold LeafCandidates.planarLaplacian
  rw [fderiv_clm_apply hdf (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hdf (differentiableAt_const Complex.I)]
  simp only [fderiv_fun_const, add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add]
  rw [hs]
  linear_combination -(1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I *
    Complex.I_sq

theorem planarLaplacian_ofReal {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    LeafCandidates.planarLaplacian (fun w => (f w : ℂ)) z =
      (LeafCandidates.realPlanarLaplacian f z : ℂ) := by
  have hF : ContDiffAt ℝ 2 (fun w => (f w : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  simp only [LeafCandidates.realPlanarLaplacian, LeafCandidates.planarLaplacian,
    fderiv_clm_apply hdF (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hdF (differentiableAt_const Complex.I),
    add_apply, ContinuousLinearMap.flip_apply, zero_add, V03Proof.secondFDeriv_ofReal hf]
  simp

theorem wirt_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => wirt f z v) := by
  have hD := hf.fderiv_right (m := ∞) (by simp)
  unfold wirt
  exact contDiff_const.mul ((hD.clm_apply contDiff_const).sub
    (contDiff_const.mul (hD.clm_apply contDiff_const)))

theorem compactDbarRealSolution_smooth {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ContDiff ℝ ∞ (compactDbarRealSolution f) := by
  have hP : ContDiff ℝ ∞ (fun w => (compactNewtonPotential f w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (L08_contDiff_logPotential_compact hf hs)
  exact contDiff_const.mul (wirt_smooth hP 1)

theorem compactDbarRealSolution_dbar {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (z : ℂ) :
    wirtBar (compactDbarRealSolution f) z 1 = (f z : ℂ) := by
  have hP : ContDiff ℝ ∞ (compactNewtonPotential f) :=
    L08_contDiff_logPotential_compact hf hs
  have hPC : ContDiff ℝ ∞ (fun w => (compactNewtonPotential f w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hP
  have hw : DifferentiableAt ℝ
      (fun w => wirt (fun u => (compactNewtonPotential f u : ℂ)) w 1) z :=
    (wirt_smooth hPC 1).contDiffAt.differentiableAt (by simp)
  unfold compactDbarRealSolution
  simp only [wirtBar, fderiv_const_mul hw, smul_apply,
    smul_eq_mul]
  have hscale : ∀ a b : ℂ,
      (1 / 2 : ℂ) * ((2 / Real.pi : ℂ) * a +
        Complex.I * ((2 / Real.pi : ℂ) * b)) =
      (2 / Real.pi : ℂ) * ((1 / 2 : ℂ) * (a + Complex.I * b)) := by
    intro a b
    ring
  rw [hscale]
  change (2 / Real.pi : ℂ) * wirtBar
    (fun w => wirt (fun u => (compactNewtonPotential f u : ℂ)) w 1) z 1 = _
  rw [wirtBar_wirt_eq_planarLaplacian (hPC.contDiffAt.of_le (by simp)),
    planarLaplacian_ofReal (hP.contDiffAt.of_le (by simp))]
  unfold compactNewtonPotential
  rw [L08_realPlanarLaplacian_logPotential_compact_eq hf hs z]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

def compactDbarSolution (b : ℂ → ℂ) (z : ℂ) : ℂ :=
  compactDbarRealSolution (fun w => (b w).re) z +
    Complex.I * compactDbarRealSolution (fun w => (b w).im) z

theorem compactDbarSolution_smooth {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hs : HasCompactSupport b) :
    ContDiff ℝ ∞ (compactDbarSolution b) := by
  exact (compactDbarRealSolution_smooth (Complex.reCLM.contDiff.comp hb)
    (hs.comp_left (by simp))).add
      (contDiff_const.mul (compactDbarRealSolution_smooth
        (Complex.imCLM.contDiff.comp hb) (hs.comp_left (by simp))))

theorem compactDbarSolution_dbar {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hs : HasCompactSupport b) (z : ℂ) :
    wirtBar (compactDbarSolution b) z 1 = b z := by
  have hre : ContDiff ℝ ∞ (fun w => (b w).re) := Complex.reCLM.contDiff.comp hb
  have him : ContDiff ℝ ∞ (fun w => (b w).im) := Complex.imCLM.contDiff.comp hb
  have hsre : HasCompactSupport (fun w => (b w).re) := hs.comp_left (by simp)
  have hsim : HasCompactSupport (fun w => (b w).im) := hs.comp_left (by simp)
  have hR : DifferentiableAt ℝ (compactDbarRealSolution (fun w => (b w).re)) z :=
    (compactDbarRealSolution_smooth hre hsre).contDiffAt.differentiableAt (by simp)
  have hJ : DifferentiableAt ℝ (compactDbarRealSolution (fun w => (b w).im)) z :=
    (compactDbarRealSolution_smooth him hsim).contDiffAt.differentiableAt (by simp)
  unfold compactDbarSolution
  rw [V03Proof.wirtBar_add _ _ z 1 hR (hJ.const_mul Complex.I)]
  have hconst : wirtBar
      (fun w => Complex.I * compactDbarRealSolution (fun w => (b w).im) w) z 1 =
      Complex.I * wirtBar (compactDbarRealSolution (fun w => (b w).im)) z 1 := by
    simp only [wirtBar, fderiv_const_mul hJ, smul_apply, smul_eq_mul]
    ring
  rw [hconst, compactDbarRealSolution_dbar hre hsre z,
    compactDbarRealSolution_dbar him hsim z]
  exact Complex.ext (by simp) (by simp)

end Yau.Blueprint.D05Proof
