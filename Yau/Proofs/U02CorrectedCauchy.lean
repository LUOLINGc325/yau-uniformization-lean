import Yau.Proofs.U02PolynomialDerivativeLower

/-! If the corrected limit has a zero differential in a direction, Cauchy
forces the actual raw differentials in that direction to decay too fast. -/

open scoped Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem raw_derivative_small_of_limit_kernel {n m : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {O : Set (ComplexVector m)} (hO : IsOpen O)
    {q : ℕ → ComplexVector m → ComplexVector n} {psi : ComplexVector m → ComplexVector n}
    (hq : ∀ᶠ k in atTop, DifferentiableOn ℂ (q k) O)
    (hpsi : DifferentiableOn ℂ psi O) {a r : ℝ} {b y : ComplexVector m}
    (ha : 0 < a) (hr : 0 < r) (hball : closedBall b (2 * r) ⊆ O)
    (hy : y ∈ closedBall b r)
    (hraw : ∀ᶠ k in atTop, ‖q k y‖ ≤ Real.exp (-a * rho o (tk k)))
    (hshadow : ∀ᶠ k in atTop, ∀ z ∈ closedBall b (2 * r),
      ‖(forwardComp G k).eval (psi z) - (H k).eval (q k z)‖ ≤ Real.exp (-6 * rho o (tk k)))
    {v : ComplexVector m} (hkernel : fderiv ℂ psi y v = 0) :
    ∀ᶠ k in atTop, ‖fderiv ℂ (q k) y v‖ ≤ Real.exp (-5 * rho o (tk k)) * ‖v‖ := by
  have hyO : y ∈ O := hball (closedBall_subset_closedBall (by linarith) hy)
  have hdpsi := (hpsi y hyO).differentiableAt (hO.mem_nhds hyO)
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  filter_upwards [hq, hraw, hshadow, models_H_derivative_lower hp ha,
    models_H_inverse_linear_exp hp (by norm_num : (0 : ℝ) < 1 / 4),
    subexponential_times_decay hp.2.1 hconst (2 / r) (23 / 4) 5 (by norm_num)]
    with k hqk hrawk hshk hlower hlin hdecay
  have hdq := (hqk y hyO).differentiableAt (hO.mem_nhds hyO)
  have hH := (polynomial_contDiff (H k)).differentiable (by simp)
  have hG := (polynomial_contDiff (forwardComp G k)).differentiable (by simp)
  have hD := V02FlowProof.norm_fderiv_sub_le_of_cauchy hO
    (hG.comp_differentiableOn hpsi) (hH.comp_differentiableOn hqk) hr
    (Real.exp_pos _).le hball hshk hy
  have hzero : fderiv ℂ (fun z => (forwardComp G k).eval (psi z)) y v = 0 := by
    change fderiv ℂ ((forwardComp G k).eval ∘ psi) y v = 0
    rw [fderiv_comp y (hG _) hdpsi, ContinuousLinearMap.comp_apply, hkernel, map_zero]
  have hrawD : fderiv ℂ (fun z => (H k).eval (q k z)) y v =
      fderiv ℂ (H k).eval (q k y) (fderiv ℂ (q k) y v) := by
    change fderiv ℂ ((H k).eval ∘ q k) y v = _
    rw [fderiv_comp y (hH _) hdq, ContinuousLinearMap.comp_apply]
  have hpoint :=
    (fderiv ℂ (fun z => (forwardComp G k).eval (psi z)) y -
      fderiv ℂ (fun z => (H k).eval (q k z)) y).le_opNorm v
  rw [ContinuousLinearMap.sub_apply, hzero, zero_sub, norm_neg, hrawD] at hpoint
  have hpoint' := hpoint.trans (mul_le_mul_of_nonneg_right hD (norm_nonneg v))
  have hA0 : 0 ≤ matOpNorm (H k).linearPart⁻¹ := norm_nonneg _
  calc
    ‖fderiv ℂ (q k) y v‖ ≤ 2 * matOpNorm (H k).linearPart⁻¹ *
        ‖fderiv ℂ (H k).eval (q k y) (fderiv ℂ (q k) y v)‖ :=
      hlower _ hrawk _
    _ ≤ 2 * Real.exp ((1 / 4) * rho o (tk k)) *
        (Real.exp (-6 * rho o (tk k)) / r * ‖v‖) := by gcongr
    _ = ((2 / r) * Real.exp (-(23 / 4) * rho o (tk k))) * ‖v‖ := by
      rw [show 2 * Real.exp ((1 / 4) * rho o (tk k)) *
          (Real.exp (-6 * rho o (tk k)) / r * ‖v‖) =
          (2 / r) * (Real.exp ((1 / 4) * rho o (tk k)) *
            Real.exp (-6 * rho o (tk k))) * ‖v‖ by ring, ← Real.exp_add]
      congr 3
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by simpa only [zero_mul, Real.exp_zero, mul_one] using hdecay) (norm_nonneg v)

end Yau.NodeProofs.U02Proof
