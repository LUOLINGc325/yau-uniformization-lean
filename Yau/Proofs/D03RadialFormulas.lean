import Yau.Proofs.D03RadialCalculus

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

private theorem log_norm_sq_half (z : ℂ) : Real.log (‖z‖ ^ 2) / 2 = Real.log ‖z‖ := by
  rw [Real.log_pow]
  norm_num

/-- The logarithmic radial chain rule, without a logarithm at the origin. -/
theorem wirtBar_log_norm_comp (F : ℝ → ℝ) {z : ℂ} (hz : z ≠ 0) {d : ℝ}
    (hF : HasDerivAt F d (Real.log ‖z‖)) :
    wirtBar (fun w : ℂ => (F (Real.log ‖w‖) : ℂ)) z 1 =
      (d : ℂ) / (2 * star z) := by
  have hpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hf : HasDerivAt F d (Real.log (‖z‖ ^ 2) / 2) := by
    rw [log_norm_sq_half]
    exact hF
  have hcomp : HasDerivAt (fun u : ℝ => F (Real.log u / 2))
      (d * ((‖z‖ ^ 2)⁻¹ / 2)) (‖z‖ ^ 2) :=
    hf.comp (‖z‖ ^ 2) ((Real.hasDerivAt_log hpos.ne').div_const 2)
  have hd := wirtBar_normSq_comp (fun u => F (Real.log u / 2)) hcomp
  simp only [log_norm_sq_half] at hd
  rw [hd]
  have he : (((‖z‖ ^ 2 : ℝ) : ℂ)) = z * star z := by
    simpa only [Complex.normSq_eq_norm_sq, starRingEnd_apply] using (Complex.mul_conj z).symm
  push_cast at he ⊢
  rw [he]
  field_simp

theorem wirtBar_log_norm {z : ℂ} (hz : z ≠ 0) :
    wirtBar (fun w : ℂ => (Real.log ‖w‖ : ℂ)) z 1 = 1 / (2 * star z) := by
  simpa using wirtBar_log_norm_comp id hz (hasDerivAt_id _)

def cutoffScalar (n : ℕ) (z : ℂ) : ℝ :=
  radialChi (Real.log ‖z‖ / correctionParameter n)

def weightScalar (n : ℕ) (z : ℂ) : ℝ :=
  (2 / correctionParameter n) * Real.log ‖z‖ + ‖z‖ ^ (1 / correctionParameter n)

theorem cutoffScalar_wirtBar (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    wirtBar (fun w : ℂ => (cutoffScalar n w : ℂ)) z 1 =
      ((deriv radialChi (Real.log ‖z‖ / correctionParameter n) : ℝ) : ℂ) /
        (2 * (correctionParameter n : ℂ) * star z) := by
  have hchi : HasDerivAt radialChi
      (deriv radialChi (Real.log ‖z‖ / correctionParameter n))
      (Real.log ‖z‖ / correctionParameter n) :=
    (radialChi_contDiff.differentiable (by simp) _).hasDerivAt
  have harg : HasDerivAt (fun u : ℝ => u / correctionParameter n)
      (1 / correctionParameter n) (Real.log ‖z‖) :=
    (hasDerivAt_id _).div_const _
  have hcomp := hchi.comp (Real.log ‖z‖) harg
  have hd := wirtBar_log_norm_comp (fun u => radialChi (u / correctionParameter n)) hz hcomp
  change _ = _ at hd
  rw [show (fun w : ℂ => (cutoffScalar n w : ℂ)) =
    (fun w : ℂ => (radialChi (Real.log ‖w‖ / correctionParameter n) : ℂ)) from rfl]
  rw [hd]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The logarithmic term has zero Levi form; the power term is strictly positive. -/
theorem weightScalar_levi (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    wirt (fun w : ℂ => wirtBar (fun v : ℂ => (weightScalar n v : ℂ)) w 1) z 1 =
      (((4 * correctionParameter n ^ 2)⁻¹ *
        ‖z‖ ^ (1 / correctionParameter n - 2) : ℝ) : ℂ) := by
  let t := correctionParameter n
  let p : ℝ := 1 / (2 * t)
  let H : ℝ → ℝ := fun u => Real.log u / t + u ^ p
  let H' : ℝ → ℝ := fun u => u⁻¹ / t + p * u ^ (p - 1)
  let u : ℝ := ‖z‖ ^ 2
  have hu : 0 < u := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have ht : t ≠ 0 := correctionParameter_ne_zero n
  have hH : ∀ v : ℝ, 0 < v → HasDerivAt H (H' v) v := by
    intro v hv
    exact ((Real.hasDerivAt_log hv.ne').div_const t).add
      (Real.hasDerivAt_rpow_const (Or.inl hv.ne'))
  let d : ℝ := -(u ^ 2)⁻¹ / t + p * ((p - 1) * u ^ ((p - 1) - 1))
  have hH' : HasDerivAt H' d u :=
    ((hasDerivAt_inv hu.ne').div_const t).add
      ((Real.hasDerivAt_rpow_const (Or.inl hu.ne')).const_mul p)
  have he := levi_normSq_comp H H' hz hH hH'
  have hfun : ∀ w : ℂ, weightScalar n w = H (‖w‖ ^ 2) := by
    intro w
    dsimp [weightScalar, H]
    rw [Real.log_pow, ← Real.rpow_natCast_mul (norm_nonneg w) 2 p]
    norm_num only [Nat.cast_ofNat]
    have hp : (2 : ℝ) * p = 1 / t := by dsimp [p]; field_simp
    rw [hp]
    dsimp [t]
    ring
  simp_rw [hfun]
  rw [he]
  congr 1
  have halg : d * u + H' u = p ^ 2 * u ^ (p - 1) := by
    dsimp [d, H']
    rw [Real.rpow_sub_one hu.ne' (p - 1)]
    field_simp
    ring
  rw [show d * ‖z‖ ^ 2 + H' (‖z‖ ^ 2) = d * u + H' u from rfl, halg]
  have hp : p ^ 2 = (4 * t ^ 2)⁻¹ := by dsimp [p]; field_simp; ring
  have hr : u ^ (p - 1) = ‖z‖ ^ (1 / t - 2) := by
    dsimp [u]
    rw [← Real.rpow_natCast_mul (norm_nonneg z) 2 (p - 1)]
    congr 1
    dsimp [p]
    field_simp
  rw [hp, hr]

variable {M : ComplexManifold 1}

theorem discDbarScalar_cutoff (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    discDbarScalar c (cutoff c n) x =
      ((deriv radialChi (Real.log ‖c x‖ / correctionParameter n) : ℝ) : ℂ) /
        (2 * (correctionParameter n : ℂ) * star (c x)) := by
  unfold discDbarScalar
  have he : (fun z : ℂ => (cutoff c n (c.symm z) : ℂ)) =ᶠ[𝓝 (c x)]
      (fun z : ℂ => (cutoffScalar n z : ℂ)) := by
    filter_upwards [B01Aux.puncturedUnitDisc_isOpen.mem_nhds (B01Aux.disc_mem c hc x)] with z hz
    simp only [cutoff, cutoffScalar, radialChi, B01Aux.disc_right_inv c hc hz]
  rw [wirtBar_eventuallyEq he]
  exact cutoffScalar_wirtBar n (norm_pos_iff.mp (B01Aux.disc_mem c hc x).1)


theorem discLeviScalar_weight (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    discLeviScalar c (weight c n) x =
      (4 * correctionParameter n ^ 2)⁻¹ * ‖c x‖ ^ (1 / correctionParameter n - 2) := by
  unfold discLeviScalar
  have he : (fun z : ℂ =>
      wirtBar (fun w : ℂ => (weight c n (c.symm w) : ℂ)) z 1) =ᶠ[𝓝 (c x)]
      (fun z : ℂ => wirtBar (fun w : ℂ => (weightScalar n w : ℂ)) z 1) := by
    filter_upwards [B01Aux.puncturedUnitDisc_isOpen.mem_nhds (B01Aux.disc_mem c hc x)] with z hz
    apply wirtBar_eventuallyEq
    filter_upwards [B01Aux.puncturedUnitDisc_isOpen.mem_nhds hz] with w hw
    simp only [weight, weightScalar, B01Aux.disc_right_inv c hc hw]
  rw [wirt_eventuallyEq he, weightScalar_levi n
    (norm_pos_iff.mp (B01Aux.disc_mem c hc x).1), Complex.ofReal_re]

end Yau.Proofs.D03Aux
