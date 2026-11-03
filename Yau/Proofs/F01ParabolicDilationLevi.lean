import Yau.Proofs.F01ParabolicDilation
import Yau.Proofs.F01TransformedMatrixIdentity

/-! The normalized potential has exactly the original complex Hessian
at the dilated point; the reciprocal potential factor cancels the two
spatial derivatives, without a bound for the full real Hessian. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem parabolicRescalePotential_levi {F : Point n → ℝ} {ρ : ℝ} (hρ : ρ ≠ 0)
    {z : Space n} {t : ℝ}
    (hF : ContDiffAt ℝ 2 (fun w => F (w, ρ ^ 2 * t)) (ρ • z)) :
    leviC (fun w => parabolicRescalePotential ρ F (w, t)) z =
      leviC (fun w => F (w, ρ ^ 2 * t)) (ρ • z) := by
  have hd : ContDiffAt ℝ 2 (fun w : Space n => ρ • w) z := by fun_prop
  have hc : ContDiffAt ℝ 2 (fun w => F (ρ • w, ρ ^ 2 * t)) z := hF.comp z hd
  change leviC (fun w => (ρ ^ 2)⁻¹ * F (ρ • w, ρ ^ 2 * t)) z = _
  have hs : leviC (fun w => (ρ ^ 2)⁻¹ * F (ρ • w, ρ ^ 2 * t)) z =
      (((ρ ^ 2)⁻¹ : ℝ) : ℂ) • leviC (fun w => F (ρ • w, ρ ^ 2 * t)) z :=
    Yau.LeafProofs.L17Aux.leviC_const_mul hc ((ρ ^ 2)⁻¹)
  rw [hs,
    leviC_spatial_dilation hF, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (pow_ne_zero 2 hρ), Complex.ofReal_one, one_smul]

theorem parabolicRescalePotential_clamped_matrix
    (A : Space n → Matrix (Fin n) (Fin n) ℂ) {F : Point n → ℝ} {ρ r T : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hF : ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T))
    {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1)
    (hA : ContDiffAt ℝ 2 (fun w => Real.log (A w).det.re) (ρ • p.1)) :
    clampedBackground (fun z => A (ρ • z)) p + complexHessianMap
      (hessian (forwardZeroSpaceTime (parabolicRescalePotential ρ F)) p) =
      if p.2 ≤ 0 then iota (A (ρ • p.1)) else
        iota (A (ρ • p.1) - ((ρ ^ 2 * p.2 : ℝ) : ℂ) • backgroundRicci A (ρ • p.1) +
          leviC (fun w => F (w, ρ ^ 2 * p.2)) (ρ • p.1)) := by
  rw [clamped_transformed_matrix_identity (fun z => A (ρ • z)) isOpen_ball
    (parabolicRescalePotential_smooth hρ hρr hρT hF) hp.1 hp.2.2]
  by_cases ht : p.2 ≤ 0
  · simp only [ht, ite_true]
  · simp only [ht, ite_false]
    rw [backgroundRicci_spatial_dilation A hA]
    have hpt : p ∈ ball 0 1 ×ˢ Icc 0 1 := ⟨hp.1, (lt_of_not_ge ht).le, hp.2.2⟩
    have hm := parabolicDilation_maps_positive hρ hρr hρT hpt
    rw [parabolicRescalePotential_levi hρ.ne'
      (closed_slab_slice_jets hF isOpen_ball hm.1 hm.2).1, smul_smul]
    have he : (p.2 : ℂ) * ((ρ ^ 2 : ℝ) : ℂ) = ((ρ ^ 2 * p.2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he]

end Yau.NodeProofs.F01Aux
