import Yau.Proofs.P06HodgeRegularityJointDerivative

/-! The actual bounded spatial jet maps turn a Hilbert C∞ curve into a
jointly C∞ scalar chart field. This proves the full Fréchet regularity. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux

variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]

theorem regularityJetCurve_contDiffOn
    (b : Basis ι ℝ E) (R : H → E → ℝ) (hR : ∀ f, ContDiff ℝ ∞ (R f))
    (L : List ι → H →L[ℝ] (E →ᵇ ℝ))
    (hL : ∀ w f z, L w f z = regularityCoefficientWord b w (R f) z)
    {T : Set ℝ} (hT : IsOpen T) {h : ℝ → H} (hh : ContDiffOn ℝ ∞ h T) (w : List ι) :
    ContDiffOn ℝ ∞ (regularityJetCurve L h w) (Set.univ ×ˢ T) := by
  have hfinite : ∀ m : ℕ, ∀ (h : ℝ → H), ContDiffOn ℝ ∞ h T → ∀ w : List ι,
      ContDiffOn ℝ m (regularityJetCurve L h w) (Set.univ ×ˢ T) := by
    intro m
    induction m with
    | zero =>
      intro h hh w
      exact contDiffOn_zero.mpr (regularityJetCurve_continuousOn L hh.continuousOn w)
    | succ m ih =>
      intro h hh w
      rw [show ((m+1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 by simp]
      apply contDiffOn_succ_of_fderiv_apply
      · intro p hp
        exact (regularityJetCurve_hasFDerivAt b R hR L hL hT hh w hp).differentiableAt.differentiableWithinAt
      · intro hm
        simp at hm
      · intro dp
        have hdh : ContDiffOn ℝ ∞ (deriv h) T := hh.deriv_of_isOpen hT (by simp)
        have hc : ContDiffOn ℝ (m : ℕ∞ω)
            (fun p => (∑ i, b.repr dp.1 i * regularityJetCurve L h (i::w) p) +
              dp.2 * regularityJetCurve L (deriv h) w p) (Set.univ ×ˢ T) :=
          (ContDiffOn.sum fun i _ => contDiffOn_const.mul (ih h hh (i::w))).add
            (contDiffOn_const.mul (ih (deriv h) hdh w))
        apply hc.congr
        intro p hp
        rw [fderivWithin_of_isOpen (isOpen_univ.prod hT) hp,
          regularityJetCurve_fderiv_apply b R hR L hL hT hh w hp]
  exact contDiffOn_infty.mpr (fun m => hfinite m h hh w)

end Yau.NodeProofs.P06Aux
