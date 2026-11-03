import Yau.Proofs.P06HodgeRegularityCanonicalTime

/-! Positive restart glues the actual local space-time chart representatives
of an arbitrary original strong Hodge heat path. Equality holds at every time. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def hodgeStrongChartScalar {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (t : ℝ) : ComplexVector n → ℝ :=
  if ht : 0 < t then hodgeCanonicalChart g μ hμ (t/2) (by positivity) x b χ hχ hcχ hχO c (h (t/2))
  else 0

theorem hodgeStrongChartScalar_ae {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) {t : ℝ} (ht : 0 < t) :
    hodgeStrongChartScalar g μ hμ h x b χ hχ hcχ hχO c t =ᵐ[lebesgueC n]
      (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap (h t) : ComplexVector n → ℝ) := by
  have hhalf : 0 < t/2 := by positivity
  have hr := hodgeStrongPath_translate g μ hμ k h hheat hhalf (t/2) hhalf
  rw [show t/2+t/2=t by ring] at hr
  simp only [hodgeStrongChartScalar,dif_pos ht]
  rw [hr]
  exact (hodgeCanonicalChart_properties g μ hμ (t/2) hhalf x b χ hχ hcχ hχO c (h (t/2))).2.2

theorem hodgeStrongChartScalar_restart {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α)
    (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : a < t) :
    hodgeStrongChartScalar g μ hμ h x b χ hχ hcχ hχO c t =
      hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c (h (t-a)) := by
  letI : (lebesgueC n).IsOpenPosMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  have ht0 : 0 < t := ha.trans ht
  have hcanon := hodgeCanonicalChart_properties g μ hμ a ha x b χ hχ hcχ hχO c (h (t-a))
  have hr := hodgeStrongPath_translate g μ hμ k h hheat (show 0 < t-a by linarith) a ha
  rw [show t-a+a=t by ring] at hr
  have hAE := hcanon.2.2
  rw [← hr] at hAE
  have hleft : ContDiff ℝ ∞ (hodgeStrongChartScalar g μ hμ h x b χ hχ hcχ hχO c t) := by
    simp only [hodgeStrongChartScalar,dif_pos ht0]
    exact (hodgeCanonicalChart_properties g μ hμ (t/2) (by positivity) x b χ hχ hcχ hχO c (h (t/2))).1
  exact Measure.eq_of_ae_eq ((hodgeStrongChartScalar_ae g μ hμ h hheat x b χ hχ hcχ hχO c ht0).trans hAE.symm)
    hleft.continuous hcanon.1.continuous

theorem hodgeStrongChartScalar_joint_contDiffOn {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      hodgeStrongChartScalar g μ hμ h x b χ hχ hcχ hχO c p.2 p.1) (Set.univ ×ˢ Set.Ioi 0) := by
  apply (isOpen_univ.prod isOpen_Ioi).contDiffOn_iff.mpr
  intro p hp
  have ht : 0 < p.2 := hp.2
  let a := p.2/2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hsmall : a < p.2 := by dsimp only [a]; linarith
  have hh : ContDiffOn ℝ ∞ (fun t => h (t-a)) (Set.Ioi a) :=
    (hodgeStrongPath_contDiffOn g μ hμ k h hheat).comp
      (contDiff_id.sub contDiff_const).contDiffOn (fun t ht => by change a < t at ht; change 0 < t-a; linarith)
  have hlocal := hodgeCanonicalChart_joint_contDiffOn g μ hμ a ha x b χ hχ hcχ hχO c isOpen_Ioi
    (fun t => h (t-a)) hh
  have hat := hlocal.contDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds (show p ∈ Set.univ ×ˢ Set.Ioi a from ⟨Set.mem_univ _,hsmall⟩))
  apply hat.congr_of_eventuallyEq
  filter_upwards [((isOpen_univ.prod isOpen_Ioi).mem_nhds (show p ∈ Set.univ ×ˢ Set.Ioi a from ⟨Set.mem_univ _,hsmall⟩))] with q hq
  exact congrFun (hodgeStrongChartScalar_restart g μ hμ h hheat x b χ hχ hcχ hχO c a ha hq.2) q.1

end Yau.NodeProofs.P06Aux
