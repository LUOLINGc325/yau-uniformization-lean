import Yau.LeafProofs.L05PerturbationActualJetsRemainder
import Yau.LeafProofs.L05PerturbationPolynomials

open Filter Asymptotics Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- The two native Frechet jets vanish when the actual C2 function is little-o of norm squared. -/
theorem perturb_actual_two_jet_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0)
    (hsmall : f =o[𝓝 (0 : V)] (fun x => ‖x‖ ^ 2)) :
    fderiv ℝ f 0 = 0 ∧ fderiv ℝ (fderiv ℝ f) 0 = 0 := by
  have hfirst : f =o[𝓝 (0 : V)] (fun x => x) :=
    hsmall.trans_isBigO (isLittleO_norm_pow_id (show 1 < 2 by decide)).isBigO
  have hD : HasFDerivAt f (0 : V →L[ℝ] ℝ) 0 := by
    apply hasFDerivAt_iff_isLittleO.mpr
    simpa only [hf0, sub_zero, zero_apply] using hfirst
  have hd := hD.fderiv
  refine ⟨hd, ?_⟩
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hp := perturb_actual_second_peano hf
  have hpeano : (fun x => f x - (1 / 2 : ℝ) * B x x) =o[𝓝 (0 : V)] (fun x => ‖x‖ ^ 2) := by
    simpa only [hf0, hd, zero_apply, sub_zero] using hp
  have hquad : (fun x => B x x) =o[𝓝 (0 : V)] (fun x => ‖x‖ ^ 2) := by
    convert (hsmall.sub hpeano).const_mul_left 2 using 1
    funext x
    ring
  have hdiag := perturb_actual_quadratic_zero B hquad
  have hsym : ∀ v w, B v w = B w v := hf.isSymmSndFDerivAt (by norm_num)
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have h := hdiag (v + w)
  simp only [map_add, add_apply] at h
  rw [hdiag v, hdiag w, hsym w v] at h
  change B v w = 0
  linarith

/-- Actual spatial jets are fixed by the literal high-order parabolic polynomial error. -/
theorem perturb_actual_spatial_identification {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {eta E r0 c q : ℝ}
    (heta : 0 < eta) (hr0 : 0 < r0) (b : Space n →L[ℝ] ℝ) (A : Sym n)
    (hc : c = u (0, 0))
    (herr : ∀ r : ℝ, 0 < r → r ≤ r0 →
      ∀ p ∈ perturbClosed (0 : Space n) r 0,
        |u p - perturbPolynomial c b A q p| ≤ E * r ^ (2 + eta)) :
    b = spatialD u (0, 0) ∧ A = hessian u (0, 0) := by
  have h0 : ((0, 0) : Point n) ∈ backward 1 := by norm_num [backward]
  have hslice := hu.2.2.2.2.1 (0, 0) h0
  let f : Space n → ℝ := fun x => u (x, 0) - perturbPolynomial c b A q (x, 0)
  have hpoly : ContDiffAt ℝ 2 (fun x : Space n => perturbPolynomial c b A q (x, 0)) 0 :=
    ((perturb_polynomial_smooth c b A q).contDiffAt.comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  have hf : ContDiffAt ℝ 2 f 0 := hslice.sub hpoly
  have hf0 : f 0 = 0 := by simp [f, perturbPolynomial, perturbQuad_eq_bilinear, hc]
  have hsmall : f =o[𝓝 (0 : Space n)] (fun x => ‖x‖ ^ 2) :=
    perturb_actual_error_littleO heta hr0 hf0 (by
      intro r hr hrb x hx
      exact herr r hr hrb (x, 0) ⟨by simpa using hx, by nlinarith [sq_nonneg r], le_rfl⟩)
  obtain ⟨hdf, hddf⟩ := perturb_actual_two_jet_zero hf hf0 hsmall
  have hspatial : fderiv ℝ f 0 = spatialD u (0, 0) - b := by
    have hd := hslice.differentiableAt (by norm_num)
    have hp := perturb_polynomial_spatial_hasFDerivAt c b A q 0 0
    convert! (hd.hasFDerivAt.sub hp).fderiv using 1
    simp only [map_zero, add_zero, spatialD]
  have hb : b = spatialD u (0, 0) := by rw [hspatial] at hdf; exact (sub_eq_zero.mp hdf).symm
  have hnear : (fun x : Space n => fderiv ℝ f x) =ᶠ[𝓝 0]
      (fun x => spatialD u (x, 0) - (b + perturbBilinear A x)) := by
    filter_upwards [hslice.eventually (by norm_num)] with x hx
    exact ((hx.differentiableAt (by norm_num)).hasFDerivAt.sub
      (perturb_polynomial_spatial_hasFDerivAt c b A q 0 x)).fderiv
  have hdd : fderiv ℝ (fderiv ℝ f) 0 = spatialDD u (0, 0) - perturbBilinear A := by
    rw [hnear.fderiv_eq]
    have hd := ((hslice.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    exact (hd.sub ((perturbBilinear A).hasFDerivAt.const_add b)).fderiv
  have hB : spatialDD u (0, 0) = perturbBilinear A := by
    rw [hdd] at hddf
    exact sub_eq_zero.mp hddf
  refine ⟨hb, ?_⟩
  have hh : hessian u (0, 0) = A := by
    unfold hessian
    simp only [hB, perturbBilinear_realVec]
    apply Subtype.ext
    exact IsSelfAdjoint.coe_selfAdjointPart_apply ℝ A.property
  exact hh.symm

end Yau.LeafProofs.L05Aux
