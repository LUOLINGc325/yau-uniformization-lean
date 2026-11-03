import Yau.Proofs.C03MovingJets
import Yau.Proofs.C03FieldEnvelope
import Yau.Proofs.P02PlanarTrace

/-! The explicit holomorphic endpoint germ preserves the full scalar Levi
trace; its quadratic correction contributes no trace term. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L22Aux
open Yau.NodeProofs.P02Aux
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ}

theorem planarTrace_quadratic_endpoint (ψ : ComplexVector n → ℝ)
    (y V Q : ComplexVector n) (hψ : ContDiffAt ℝ 2 ψ y) :
    planarTrace (fun a : ℂ => ψ (y + a • V + ((1 / 2 : ℂ) * a ^ 2) • Q)) 0 =
      4 * complexLeviQuadratic ψ y V := by
  let e := movingTrial (fun _ => y) (fun _ => V) Q 1
  have heq : e = fun a : ℂ => y + a • V + ((1 / 2 : ℂ) * a ^ 2) • Q := by
    funext a
    exact movingTrial_terminal (fun _ => y) (fun _ => V) Q a
  have he : ContDiff ℂ 2 e := by
    dsimp only [e, movingTrial]
    exact (contDiff_const.add (contDiff_id.smul contDiff_const)).add
      ((contDiff_const.mul (contDiff_id.pow 2)).smul_const Q)
  have her : ContDiffAt ℝ 2 e 0 := (he.restrict_scalars ℝ).contDiffAt
  have he0 : e 0 = y := movingTrial_zero_parameter _ _ Q 1
  have hf1 : fderiv ℝ e 0 (1 : ℂ) = V := by
    simpa only [e, mapDirection, mul_zero, zero_smul, add_zero, one_smul] using
      movingTrial_mapDirection (fun _ => y) (fun _ => V) Q 1 0 1
  have hfI : fderiv ℝ e 0 Complex.I = Complex.I • V := by
    simpa only [e, mapDirection, mul_zero, zero_smul, add_zero] using
      movingTrial_mapDirection (fun _ => y) (fun _ => V) Q 1 0 Complex.I
  have hd (a : ℂ) : mapDirection (mapDirection e a) a 0 =
      fderiv ℝ (fderiv ℝ e) 0 a a := by
    have H := (mapDirection_hasFDerivAt e (p := (0 : ℂ)) her a).fderiv
    have HH := congrArg (fun L : ℂ →L[ℝ] ComplexVector n => L a) H
    exact HH
  have hs : fderiv ℝ (fderiv ℝ e) 0 1 1 +
      fderiv ℝ (fderiv ℝ e) 0 Complex.I Complex.I = 0 := by
    rw [← hd 1, ← hd Complex.I]
    exact movingTrial_radial_trace_zero (fun _ => y) (fun _ => V) Q 1 0
  have hψe : ContDiffAt ℝ 2 ψ (e 0) := by rwa [he0]
  have H1 := L18Aux.secondFDeriv_comp her hψe (1 : ℂ) (1 : ℂ)
  have HI := L18Aux.secondFDeriv_comp her hψe Complex.I Complex.I
  have hz : fderiv ℝ ψ (e 0) (fderiv ℝ (fderiv ℝ e) 0 1 1) +
      fderiv ℝ ψ (e 0) (fderiv ℝ (fderiv ℝ e) 0 Complex.I Complex.I) = 0 := by
    rw [← map_add, hs, map_zero]
  have hcomp : (fun a : ℂ => ψ (y + a • V + ((1 / 2 : ℂ) * a ^ 2) • Q)) = ψ ∘ e := by
    rw [heq]
    rfl
  rw [hcomp]
  unfold planarTrace
  change fderiv ℝ (fderiv ℝ (ψ ∘ e)) 0 1 1 +
    fderiv ℝ (fderiv ℝ (ψ ∘ e)) 0 Complex.I Complex.I = _
  rw [H1, HI, hf1, hfI]
  rw [he0] at hz ⊢
  unfold complexLeviQuadratic
  linarith

theorem quadratic_endpoint_contDiffAt (ψ : ComplexVector n → ℝ)
    (y V Q : ComplexVector n) (hψ : ContDiffAt ℝ 2 ψ y) :
    ContDiffAt ℝ 2 (fun a : ℂ => ψ (y + a • V + ((1 / 2 : ℂ) * a ^ 2) • Q)) 0 := by
  have he : ContDiff ℂ 2 (fun a : ℂ => y + a • V + ((1 / 2 : ℂ) * a ^ 2) • Q) :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).add
      ((contDiff_const.mul (contDiff_id.pow 2)).smul_const Q)
  have hψe : ContDiffAt ℝ 2 ψ (y + (0 : ℂ) • V + ((1 / 2 : ℂ) * (0 : ℂ) ^ 2) • Q) := by
    simpa only [zero_smul, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hψ
  exact hψe.comp 0 (he.restrict_scalars ℝ).contDiffAt

end Yau.Proofs.C03Aux
