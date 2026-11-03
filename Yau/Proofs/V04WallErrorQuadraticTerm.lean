import Yau.Proofs.V04WallErrorMixedCalculus

/-! The actual mixed derivative of one sesquilinear fiber term. -/

open scoped Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedWirt_sesquilinear_term
    (L R : E →L[ℂ] ℂ) {c : E → ℂ} {z : E}
    (hc : ContDiffAt ℝ 2 c z) (v w : E) :
    wirt (fun y => wirtBar (fun x => star (L x) * c x * R x) y v) z w =
      star (L v) * (wirt c z w * R z + c z * R w) +
        star (L z) * (wirt (fun y => wirtBar c y v) z w * R z + wirtBar c z v * R w) := by
  have hL : ContDiffAt ℝ 2 (fun x => star (L x)) z :=
    (Complex.conjCLE.contDiff.comp (L.restrictScalars ℝ).contDiff).contDiffAt
  have hR : ContDiffAt ℝ 2 (fun x => R x) z := (R.restrictScalars ℝ).contDiff.contDiffAt
  have hLD := hL.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hcD := hc.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  rw [mixedWirt_mul (hL.mul hc) hR v w, mixedWirt_mul hL hc v w,
    wirtBar_mul hLD hcD v, wirt_mul hLD hcD w,
    wirt_complexLinear R z w, wirtBar_complexLinear R z v,
    mixedWirt_complexLinear R z v w, wirt_star_complexLinear L z w,
    wirtBar_star_complexLinear L z v, mixedWirt_star_complexLinear L z v w]
  ring

end Yau.Blueprint.V04Proof.WallErrorAux
