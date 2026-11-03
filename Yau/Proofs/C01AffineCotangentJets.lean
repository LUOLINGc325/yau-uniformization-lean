import Yau.Proofs.C01WirtingerProducts

/-! Actual holomorphic cotangent first jets, restricted to the affine
complex line used to test the joint Levi matrix. -/

noncomputable section

open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint.Alignment.Y03Proof

theorem affine_wirt (c d z : ℂ) :
    wirt (fun p : ℂ => c + p * d) z 1 = d := by
  have hd : HasDerivAt (fun p : ℂ => c + p * d) d z := by
    simpa only [one_mul, id_eq] using! ((hasDerivAt_id z).mul_const d).const_add c
  rw [wirt_of_differentiableAt_complex hd.differentiableAt, hd.hasFDerivAt.fderiv]
  simp

theorem affine_wirtBar (c d z : ℂ) :
    wirtBar (fun p : ℂ => c + p * d) z 1 = 0 := by
  apply wirtBar_of_differentiableAt_complex
  fun_prop

theorem wirt_conjugate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℂ) (z v : V) :
    wirt (fun p => star (f p)) z v = star (wirtBar f z v) := by
  unfold wirt wirtBar
  rw [fderiv_star]
  simp [star_mul, star_add]
  ring

theorem wirtBar_conjugate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℂ) (z v : V) :
    wirtBar (fun p => star (f p)) z v = star (wirt f z v) := by
  unfold wirtBar wirt
  rw [fderiv_star]
  simp [star_mul, star_sub, Complex.star_def]
  ring

theorem conjugateAffine_wirt (c d z : ℂ) :
    wirt (fun p : ℂ => star (c + p * d)) z 1 = 0 := by
  rw [wirt_conjugate, affine_wirtBar, star_zero]

theorem conjugateAffine_wirtBar (c d z : ℂ) :
    wirtBar (fun p : ℂ => star (c + p * d)) z 1 = star d := by
  rw [wirtBar_conjugate, affine_wirt]

theorem affine_mixed_wirt (c d z : ℂ) :
    wirt (fun p => wirtBar (fun q : ℂ => c + q * d) p 1) z 1 = 0 := by
  simp only [affine_wirtBar]
  simp [wirt]

theorem conjugateAffine_mixed_wirt (c d z : ℂ) :
    wirt (fun p => wirtBar (fun q : ℂ => star (c + q * d)) p 1) z 1 = 0 := by
  simp only [conjugateAffine_wirtBar]
  simp [wirt]

end Yau.NodeProofs.C01Aux
