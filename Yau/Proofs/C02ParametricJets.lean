import Yau.Proofs.C02ParametricSmooth

/-! Actual iterated derivatives commute with the compact radial integral.
The recursion changes the target Banach space at each derivative, while
currying is an isometry and introduces no factorial or dimension loss. -/

noncomputable section
open scoped Interval ContDiff
universe u
namespace Yau.Blueprint.C02Proof
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def parametricJet (m : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E × ℝ → F) (p : E × ℝ) : E [×m]→L[ℝ] F :=
  match m with
  | 0 => (continuousMultilinearCurryFin0 ℝ E F).symm (G p)
  | k + 1 => (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
      (parametricJet k (parametricFirstDerivative G) p)

theorem parametricJet_smooth (m : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (G : E × ℝ → F), ContDiff ℝ ∞ G → ContDiff ℝ ∞ (parametricJet m G) := by
  induction m with
  | zero =>
      intro F _ _ G hG
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hG
  | succ m ih =>
      intro F _ _ G hG
      exact (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.contDiff.comp
        (ih (parametricFirstDerivative G) (parametricFirstDerivative_smooth G hG))

theorem parametricJet_eq_iteratedFDeriv (m : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (G : E × ℝ → F), ContDiff ℝ ∞ G → ∀ x t,
      parametricJet m G (x, t) = iteratedFDeriv ℝ m (fun y => G (y, t)) x := by
  induction m with
  | zero => intro F _ _ G hG x t; rfl
  | succ m ih =>
      intro F _ _ G hG x t
      have hD : fderiv ℝ (fun y => G (y, t)) =
          fun y => parametricFirstDerivative G (y, t) :=
        funext (fun y => (parametricFirstDerivative_hasFDeriv G hG y t).fderiv)
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, hD]
      exact congrArg (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
        (ih (parametricFirstDerivative G) (parametricFirstDerivative_smooth G hG) x t)

variable [FiniteDimensional ℝ E]

private theorem integral_curryRight (m : ℕ)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℝ → E [×m]→L[ℝ] (E →L[ℝ] F)) :
    (∫ t in (0 : ℝ)..1, (continuousMultilinearCurryRightEquiv' ℝ m E F).symm (f t)) =
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm (∫ t in (0 : ℝ)..1, f t) := by
  have hc := (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.toLinearIsometry.intervalIntegral_comp_comm
    (𝕜 := ℝ) (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume) f
  convert hc using 1 <;> rfl

theorem parametricJet_intervalIntegral (m : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (G : E × ℝ → F), ContDiff ℝ ∞ G → ∀ x,
      (∫ t in (0 : ℝ)..1, parametricJet m G (x, t)) =
        iteratedFDeriv ℝ m (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) x := by
  induction m with
  | zero =>
      intro F _ _ _ G hG x
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.intervalIntegral_comp_comm
        (fun t => G (x, t))
  | succ m ih =>
      intro F _ _ _ G hG x
      have hD : fderiv ℝ (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) =
          fun y => ∫ t in (0 : ℝ)..1, parametricFirstDerivative G (y, t) :=
        funext (fun y => (hasFDerivAt_intervalIntegral_smooth G hG y).fderiv)
      calc
        _ = (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
            (∫ t in (0 : ℝ)..1, parametricJet m (parametricFirstDerivative G) (x, t)) := by
          change (∫ t in (0 : ℝ)..1,
            (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
              (parametricJet m (parametricFirstDerivative G) (x, t))) = _
          exact integral_curryRight m (fun t => parametricJet m (parametricFirstDerivative G) (x, t))
        _ = (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
            (iteratedFDeriv ℝ m (fun y => ∫ t in (0 : ℝ)..1,
              parametricFirstDerivative G (y, t)) x) := by
          rw [ih (parametricFirstDerivative G) (parametricFirstDerivative_smooth G hG) x]
        _ = _ := by
          rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, hD]

theorem iteratedFDeriv_intervalIntegral_smooth
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E × ℝ → F) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) x =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ m (fun y => G (y, t)) x := by
  exact (parametricJet_intervalIntegral m G hG x).symm.trans
    (congrArg (fun f : ℝ → E [×m]→L[ℝ] F => ∫ t in (0 : ℝ)..1, f t)
      (funext (fun t => parametricJet_eq_iteratedFDeriv m G hG x t)))

end Yau.Blueprint.C02Proof
