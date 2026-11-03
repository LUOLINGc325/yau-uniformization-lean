import Yau.LeafProofs.L10InteriorIntegration

/-! Moving one derivative onto the flux does not differentiate the forcing. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace Yau.LeafProofs

theorem elliptic_directional_derivatives_commute {n : ℕ}
    {u : ComplexVector n → ℂ} {x : ComplexVector n}
    (hu : ContDiffAt ℝ 2 u x) (e v : ComplexVector n) :
    fderiv ℝ (fun y => fderiv ℝ u y e) x v =
      fderiv ℝ (fun y => fderiv ℝ u y v) x e := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hD (show DifferentiableAt ℝ (fun _ : ComplexVector n => e) x by fun_prop),
    fderiv_clm_apply hD (show DifferentiableAt ℝ (fun _ : ComplexVector n => v) x by fun_prop)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using (hu.isSymmSndFDerivAt (by norm_num)).eq v e

theorem ellipticDivergence_differentiated_test_identity {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {u φ : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ O) (k : RIdx n) :
    (∫ x, fderiv ℝ φ x (realVec k) * ellipticDivergence a u x ∂lebesgueC n) =
      ∑ i, ∫ x, fderiv ℝ φ x (realVec i) *
        fderiv ℝ (ellipticFlux a u i) x (realVec k) ∂lebesgueC n := by
  classical
  have hDφ (e : ComplexVector n) : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x e) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  rw [ellipticDivergence_test_identity hO ha hu (hDφ (realVec k))
    (hcφ.fderiv_apply ℝ (realVec k))
    ((tsupport_fderiv_apply_subset ℝ (realVec k)).trans hs), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [elliptic_local_test_integration_by_parts hO (hDφ (realVec i))
    (hcφ.fderiv_apply ℝ (realVec i))
    ((tsupport_fderiv_apply_subset ℝ (realVec i)).trans hs)
    (ellipticFlux_contDiffOn hO ha hu i) (realVec k)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [elliptic_directional_derivatives_commute
    (hφ.contDiffAt.of_le (by simp)) (realVec k) (realVec i)]

theorem ellipticFlux_fderiv_expand {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) {z : ComplexVector n} (hz : z ∈ O) (i k : RIdx n) :
    fderiv ℝ (ellipticFlux a u i) z (realVec k) =
      (∑ j, (a z i j : ℂ) *
        fderiv ℝ (fun w => fderiv ℝ u w (realVec j)) z (realVec k)) +
      ∑ j, (fderiv ℝ (fun w => a w i j) z (realVec k) : ℂ) *
        fderiv ℝ u z (realVec j) := by
  classical
  have hac (j : RIdx n) : HasFDerivAt (fun w => (a w i j : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun w => a w i j) z)) z := by
    have h := ((ha i j).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.hasFDerivAt.comp z h.hasFDerivAt
  have hgrad (j : RIdx n) : DifferentiableAt ℝ (fun w => fderiv ℝ u w (realVec j)) z :=
    ((elliptic_contDiffOn_directionalDerivative hO hu (realVec j)).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hprod (j : RIdx n) :
      fderiv ℝ (fun w => (a w i j : ℂ) * fderiv ℝ u w (realVec j)) z (realVec k) =
        (a z i j : ℂ) * fderiv ℝ (fun w => fderiv ℝ u w (realVec j)) z (realVec k) +
        (fderiv ℝ (fun w => a w i j) z (realVec k) : ℂ) *
          fderiv ℝ u z (realVec j) := by
    rw [fderiv_fun_mul (hac j).differentiableAt (hgrad j), (hac j).fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    ring
  unfold ellipticFlux
  have hsum : fderiv ℝ (fun z => ∑ j, (a z i j : ℂ) * fderiv ℝ u z (realVec j)) z =
      ∑ j, fderiv ℝ (fun w => (a w i j : ℂ) * fderiv ℝ u w (realVec j)) z :=
    fderiv_fun_sum (fun j _ => (hac j).differentiableAt.mul (hgrad j))
  rw [hsum]
  simp only [sum_apply, hprod, Finset.sum_add_distrib]

theorem ellipticHessian_test_identity {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {u φ : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) O)
    (hu : ContDiffOn ℝ ∞ u O) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ O) (k : RIdx n) :
    (∫ x, fderiv ℝ φ x (realVec k) * ellipticDivergence a u x ∂lebesgueC n) =
      ∑ i, ∫ x, fderiv ℝ φ x (realVec i) *
        ((∑ j, (a x i j : ℂ) *
          fderiv ℝ (fun w => fderiv ℝ u w (realVec j)) x (realVec k)) +
          ∑ j, (fderiv ℝ (fun w => a w i j) x (realVec k) : ℂ) *
            fderiv ℝ u x (realVec j)) ∂lebesgueC n := by
  rw [ellipticDivergence_differentiated_test_identity hO ha hu hφ hcφ hs k]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ O
  · rw [ellipticFlux_fderiv_expand hO ha hu hx i k]
  · have hφzero : fderiv ℝ φ x = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))
    simp only [hφzero, zero_apply, zero_mul]

end Yau.LeafProofs
