import Yau.Proofs.P06HodgeRegularityJointCalculus

/-! Joint differentiability follows from the actual spatial derivatives
and the Hilbert time derivative, whose partials are jointly continuous. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux

variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]

theorem regularityJetCurve_hasFDerivAt
    (b : Basis ι ℝ E) (R : H → E → ℝ) (hR : ∀ f, ContDiff ℝ ∞ (R f))
    (L : List ι → H →L[ℝ] (E →ᵇ ℝ))
    (hL : ∀ w f z, L w f z = regularityCoefficientWord b w (R f) z)
    {T : Set ℝ} (hT : IsOpen T) {h : ℝ → H} (hh : ContDiffOn ℝ ∞ h T)
    (w : List ι) {p : E × ℝ} (hp : p ∈ Set.univ ×ˢ T) :
    HasFDerivAt (regularityJetCurve L h w)
      ((fderiv ℝ (regularityCoefficientWord b w (R (h p.2))) p.1).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (regularityJetCurve L (deriv h) w p))) p := by
  let S : Set (E × ℝ) := Set.univ ×ˢ T
  have hS : IsOpen S := isOpen_univ.prod hT
  let DS (q : E × ℝ) := fderiv ℝ (regularityCoefficientWord b w (R (h q.2))) q.1
  let DT (q : E × ℝ) := (1 : ℝ →L[ℝ] ℝ).smulRight (regularityJetCurve L (deriv h) w q)
  have hdh : ContDiffOn ℝ ∞ (deriv h) T := hh.deriv_of_isOpen hT (by simp)
  have hsp (q : E × ℝ) :
      HasFDerivAt (fun x => L w (h q.2) x) (DS q) q.1 := by
    have heq : (fun x => L w (h q.2) x) = regularityCoefficientWord b w (R (h q.2)) :=
      funext fun x => hL w (h q.2) x
    rw [heq]
    exact ((regularityCoefficientWord_contDiff b (hR (h q.2)) w).differentiable (by simp) q.1).hasFDerivAt
  have htime (q : E × ℝ) (hq : q ∈ S) :
      HasFDerivAt (fun t => L w (h t) q.1) (DT q) q.2 := by
    have hd : HasDerivAt h (deriv h q.2) q.2 :=
      ((hh.contDiffAt (hT.mem_nhds hq.2)).differentiableAt (by simp)).hasDerivAt
    have he := ((BoundedContinuousFunction.evalCLM ℝ q.1).comp (L w)).hasFDerivAt.comp_hasDerivAt q.2 hd
    exact he.hasFDerivAt
  have hDS : ContinuousOn DS S := by
    apply continuousOn_clm_apply.mpr
    intro dx
    have heq : (fun q => DS q dx) =
        fun q => ∑ i, b.repr dx i * regularityJetCurve L h (i::w) q := by
      funext q
      rw [regularityBasis_fderiv_apply b]
      apply Finset.sum_congr rfl
      intro i _
      rw [regularityJetCurve,hL]
      rfl
    rw [heq]
    exact continuousOn_finsetSum Finset.univ fun i _ => continuousOn_const.mul
      (regularityJetCurve_continuousOn L hh.continuousOn (i::w))
  have hDT : ContinuousOn DT S := by
    apply continuousOn_clm_apply.mpr
    intro dt
    have heq : (fun q => DT q dt) = fun q => dt * regularityJetCurve L (deriv h) w q := by
      funext q
      simp only [DT,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply,smul_eq_mul]
    rw [heq]
    exact continuousOn_const.mul (regularityJetCurve_continuousOn L hdh.continuousOn w)
  exact (hasStrictFDerivAt_uncurry_coprod (f := fun x t => L w (h t) x)
    (f₁ := fun x t => DS (x,t)) (f₂ := fun x t => DT (x,t))
    (Eventually.of_forall hsp)
    (by filter_upwards [hS.mem_nhds hp] with q hq; exact htime q hq)
    (hDS.continuousAt (hS.mem_nhds hp)) (hDT.continuousAt (hS.mem_nhds hp))).hasFDerivAt

theorem regularityJetCurve_fderiv_apply
    (b : Basis ι ℝ E) (R : H → E → ℝ) (hR : ∀ f, ContDiff ℝ ∞ (R f))
    (L : List ι → H →L[ℝ] (E →ᵇ ℝ))
    (hL : ∀ w f z, L w f z = regularityCoefficientWord b w (R f) z)
    {T : Set ℝ} (hT : IsOpen T) {h : ℝ → H} (hh : ContDiffOn ℝ ∞ h T)
    (w : List ι) {p : E × ℝ} (hp : p ∈ Set.univ ×ˢ T) (dp : E × ℝ) :
    fderiv ℝ (regularityJetCurve L h w) p dp =
      (∑ i, b.repr dp.1 i * regularityJetCurve L h (i::w) p) +
        dp.2 * regularityJetCurve L (deriv h) w p := by
  rw [(regularityJetCurve_hasFDerivAt b R hR L hL hT hh w hp).fderiv,
    ContinuousLinearMap.coprod_apply,regularityBasis_fderiv_apply b]
  simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [regularityJetCurve,hL]
  rfl

end Yau.NodeProofs.P06Aux
