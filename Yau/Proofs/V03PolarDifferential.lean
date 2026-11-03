import Yau.Proofs.V03PolarGradient
import Yau.Proofs.V03PolarRotation

/-! The actual polar flux divergence is the radial weight times the real
Laplacian, proved from native derivatives in the open disc. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def polarDiscDifferential (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (circlePoint p.2) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (p.1 • (circlePoint p.2 * Complex.I))

theorem hasFDerivAt_polarAngle (p : ℝ × ℝ) :
    HasFDerivAt (fun p' : ℝ × ℝ => circlePoint p'.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (circlePoint p.2 * Complex.I)) p := by
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_comp] using
    (hasDerivAt_circlePoint p.2).hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ))

theorem hasFDerivAt_polarAngleI (p : ℝ × ℝ) :
    HasFDerivAt (fun p' : ℝ × ℝ => circlePoint p'.2 * Complex.I)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-circlePoint p.2)) p := by
  have hh := (hasDerivAt_circlePoint p.2).mul_const Complex.I
  have hvalue : circlePoint p.2 * Complex.I * Complex.I = -circlePoint p.2 := by
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
  rw [hvalue] at hh
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_comp] using
    hh.hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ))

theorem hasFDerivAt_polarDiscPoint (p : ℝ × ℝ) :
    HasFDerivAt polarDiscPoint (polarDiscDifferential p) p := by
  have hr : HasFDerivAt (fun p' : ℝ × ℝ => (p'.1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p hasFDerivAt_fst
  have hh := hr.mul (hasFDerivAt_polarAngle p)
  change HasFDerivAt polarDiscPoint _ p at hh
  have heq : (p.1 : ℂ) •
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (circlePoint p.2 * Complex.I) +
      circlePoint p.2 • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) =
      polarDiscDifferential p := by
    apply ContinuousLinearMap.ext
    intro v
    simp [polarDiscDifferential, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc, add_comm]
  rw [heq] at hh
  exact hh

theorem fderiv_polarRadialFlux {u : ℂ → ℝ} {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo 0 1)
    (hu : ContDiffAt ℝ 2 u (polarDiscPoint p)) :
    fderiv ℝ (polarRadialFlux u) p (1, 0) =
      fderiv ℝ u (polarDiscPoint p) (circlePoint p.2) +
        p.1 * fderiv ℝ (fderiv ℝ u) (polarDiscPoint p) (circlePoint p.2) (circlePoint p.2) := by
  have hD : HasFDerivAt (fun p' => fderiv ℝ u (polarDiscPoint p'))
      ((fderiv ℝ (fderiv ℝ u) (polarDiscPoint p)).comp (polarDiscDifferential p)) p :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.comp
      p (hasFDerivAt_polarDiscPoint p)
  have hh := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul (hD.clm_apply (hasFDerivAt_polarAngle p))
  rw [(polarRadialFlux_eventually_eq hp).fderiv_eq]
  have he := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A (1, 0)) hh.fderiv
  simpa [Pi.mul_def, polarDiscDifferential, add_comm] using he

theorem fderiv_polarAngularFlux {u : ℂ → ℝ} {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo 0 1)
    (hu : ContDiffAt ℝ 2 u (polarDiscPoint p)) :
    fderiv ℝ (polarAngularFlux u) p (0, 1) =
      -fderiv ℝ u (polarDiscPoint p) (circlePoint p.2) +
        p.1 * fderiv ℝ (fderiv ℝ u) (polarDiscPoint p)
          (circlePoint p.2 * Complex.I) (circlePoint p.2 * Complex.I) := by
  have hD : HasFDerivAt (fun p' => fderiv ℝ u (polarDiscPoint p'))
      ((fderiv ℝ (fderiv ℝ u) (polarDiscPoint p)).comp (polarDiscDifferential p)) p :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.comp
      p (hasFDerivAt_polarDiscPoint p)
  have hh := hD.clm_apply (hasFDerivAt_polarAngleI p)
  rw [(polarAngularFlux_eventually_eq hp).fderiv_eq]
  have he := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A (0, 1)) hh.fderiv
  simpa only [polarDiscDifferential, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd, zero_smul, one_smul,
    zero_add, map_neg, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] using he

theorem polarFlux_divergence {u : ℂ → ℝ} {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo 0 1)
    (hu : ContDiffAt ℝ 2 u (polarDiscPoint p)) :
    fderiv ℝ (polarRadialFlux u) p (1, 0) + fderiv ℝ (polarAngularFlux u) p (0, 1) =
      p.1 * (fderiv ℝ (fderiv ℝ u) (polarDiscPoint p) 1 1 +
        fderiv ℝ (fderiv ℝ u) (polarDiscPoint p) Complex.I Complex.I) := by
  rw [fderiv_polarRadialFlux hp hu, fderiv_polarAngularFlux hp hu]
  have hrot := secondFDeriv_circle_rotation (u := u) (polarDiscPoint p) (circlePoint p.2)
  rw [circlePoint_norm, one_pow, one_mul] at hrot
  rw [mul_comm Complex.I] at hrot
  calc
    _ = p.1 * (fderiv ℝ (fderiv ℝ u) (polarDiscPoint p) (circlePoint p.2) (circlePoint p.2) +
        fderiv ℝ (fderiv ℝ u) (polarDiscPoint p)
          (circlePoint p.2 * Complex.I) (circlePoint p.2 * Complex.I)) := by ring
    _ = _ := congrArg (fun x : ℝ => p.1 * x) hrot

end Yau.Blueprint.V03Proof
