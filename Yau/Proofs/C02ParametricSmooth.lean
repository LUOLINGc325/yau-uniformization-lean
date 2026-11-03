import Yau.Proofs.C02ParametricInterval

/-! The same compact-parameter integral is smooth at every finite order.
The induction ranges over its target Banach space as the derivative target changes. -/

noncomputable section
universe u
open scoped Interval ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def parametricFirstDerivative {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E × ℝ → F) (p : E × ℝ) : E →L[ℝ] F :=
  (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem parametricFirstDerivative_smooth
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E × ℝ → F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (parametricFirstDerivative G) := by
  exact (hG.fderiv_right (by simp)).clm_comp contDiff_const

theorem parametricFirstDerivative_hasFDeriv
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E × ℝ → F) (hG : ContDiff ℝ ∞ G) (x : E) (t : ℝ) :
    HasFDerivAt (fun y => G (y, t)) (parametricFirstDerivative G (x, t)) x := by
  have hPair : HasFDerivAt (fun y : E => (y, t)) (ContinuousLinearMap.inl ℝ E ℝ) x := by
    simpa only [ContinuousLinearMap.inl, id_eq] using
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact ((hG.differentiable (by simp) (x, t)).hasFDerivAt).comp x hPair

variable [FiniteDimensional ℝ E]

theorem hasFDerivAt_intervalIntegral_smooth
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E × ℝ → F) (hG : ContDiff ℝ ∞ G) (x : E) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, G (y, t))
      (∫ t in (0 : ℝ)..1, parametricFirstDerivative G (x, t)) x := by
  exact hasFDerivAt_intervalIntegral_of_joint_continuity
    (fun y t => G (y, t)) (fun y t => parametricFirstDerivative G (y, t))
    hG.continuous (parametricFirstDerivative_smooth G hG).continuous
    (parametricFirstDerivative_hasFDeriv G hG) x

private theorem contDiff_intervalIntegral_nat (m : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (G : E × ℝ → F), ContDiff ℝ ∞ G →
      ContDiff ℝ m (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) := by
  induction m with
  | zero =>
      intro F _ _ _ G hG
      apply contDiff_zero.mpr
      exact (show Differentiable ℝ (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) from
        fun x => (hasFDerivAt_intervalIntegral_smooth G hG x).differentiableAt).continuous
  | succ m ih =>
      intro F _ _ _ G hG
      change ContDiff ℝ ((m : ℕ∞ω) + 1) (fun y => ∫ t in (0 : ℝ)..1, G (y, t))
      apply contDiff_succ_iff_fderiv.mpr
      refine ⟨fun x => (hasFDerivAt_intervalIntegral_smooth G hG x).differentiableAt,
        by simp, ?_⟩
      have hDerivative : fderiv ℝ (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) =
          fun x => ∫ t in (0 : ℝ)..1, parametricFirstDerivative G (x, t) :=
        funext (fun x => (hasFDerivAt_intervalIntegral_smooth G hG x).fderiv)
      rw [hDerivative]
      exact ih (parametricFirstDerivative G) (parametricFirstDerivative_smooth G hG)

theorem contDiff_intervalIntegral_smooth
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E × ℝ → F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) :=
  contDiff_infty.mpr (fun m => contDiff_intervalIntegral_nat m G hG)

end Yau.Blueprint.C02Proof
