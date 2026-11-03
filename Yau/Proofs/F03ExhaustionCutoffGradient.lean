import Yau.Proofs.F02Cutoff

/-! The actual controlled-exhaustion cutoffs have their genuine physical gradient bound. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux F02Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem gradNormSq_scalar_comp (g : HermitianField M) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : M.Carrier) :
    gradNormSq g (fun y => F (u y)) x = deriv F (u x)^2 * gradNormSq g u x := by
  have h := scalarGradientPair_scalar_comp_self g hu F x
    (hF.differentiable (by simp) (u x))
  rw [scalarGradientPair_eq_twice_gradNormSq g (smoothFn_scalar_comp hu F hF) x,
    scalarGradientPair_eq_twice_gradNormSq g hu x] at h
  linarith

theorem exhaustionCutoff_gradient_formula (g : HermitianField M)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (A L : ℝ) (x : M.Carrier) :
    gradNormSq g (exhaustionCutoff u A L) x =
      (deriv exhaustionCutoffProfile (u x/(A*L))/(A*L))^2 * gradNormSq g u x := by
  have hF : ContDiff ℝ ∞ (fun z : ℝ => exhaustionCutoffProfile (z/(A*L))) :=
    exhaustionCutoffProfile.contDiff.comp (contDiff_id.div_const (A*L))
  exact (gradNormSq_scalar_comp g hu _ hF x).trans
    (by rw [exhaustionCutoffProfile_scaled_deriv])

theorem exhaustionCutoff_gradient_bound (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ K : ℝ, 0 < K ∧ ∀ A,1 ≤ A → ∀ L,1 ≤ L → ∀ x,
      Real.sqrt (gradNormSq X.metric.form (exhaustionCutoff u A L) x) ≤ K/L := by
  obtain ⟨C,hC,hControl⟩ := hu.2.2.2
  obtain ⟨B,hB,hDeriv⟩ := exhaustionCutoffProfile_derivative_bounds
  refine ⟨B*C,mul_pos hB hC,fun A hA L hL x => ?_⟩
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR0 : 0 < A*L := mul_pos hA0 hL0
  have hRL : L ≤ A*L := by nlinarith
  have hg0 : 0 ≤ gradNormSq X.metric.form u x := by
    have h := scalarGradientPair_self_nonneg X.metric.form u x
    rw [scalarGradientPair_eq_twice_gradNormSq _ hu.1] at h
    linarith
  have hd : |deriv exhaustionCutoffProfile (u x/(A*L))/(A*L)| ≤ B/(A*L) := by
    rw [abs_div,abs_of_pos hR0]
    exact div_le_div_of_nonneg_right (hDeriv _).1 hR0.le
  have hBound : gradNormSq X.metric.form (exhaustionCutoff u A L) x ≤
      (B*C/(A*L))^2 := by
    rw [exhaustionCutoff_gradient_formula _ hu.1]
    calc
      _ ≤ (B/(A*L))^2*C^2 := mul_le_mul
        (by simpa only [sq_abs] using
          (pow_le_pow_left₀ (abs_nonneg _) hd 2))
        (hControl x).2.2.1 hg0 (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ Real.sqrt ((B*C/(A*L))^2) := Real.sqrt_le_sqrt hBound
    _ = B*C/(A*L) := Real.sqrt_sq (by positivity)
    _ ≤ B*C/L := div_le_div_of_nonneg_left (by positivity) hL0 hRL

end Yau.Proofs.F03Aux
