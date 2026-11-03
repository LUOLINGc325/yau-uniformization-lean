import Yau.Proofs.P06HodgeRegularityStrongChart

/-! Actual time-dependent alternating model fields transform smoothly
under every chart change, on the original chart source. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem regularityChartPushforward_joint_contDiffAt
    (x b : M.Carrier) (P : ℝ → ComplexVector n → HodgeJets.Fiber n k)
    (hP : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => P p.2 p.1) (Set.univ ×ˢ Set.Ioi 0))
    {z : ComplexVector n} (hz : z ∈ chartTarget b) {t : ℝ} (ht : 0 < t)
    (hy : chartInv b z ∈ (extChartAt (ComplexModel n) x).source) (I : Fin k → RIdx n) :
    ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ =>
      formComponents (chartFormPushforward x (P p.2)) b p.1 I) (z,t) := by
  have hi : ContinuousAt (chartInv b) z := by
    with_unfolding_all
      exact continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
  have hT : ContDiffAt ℝ ∞ (fun y => chartPt x (chartInv b y)) z :=
    (L18Aux.chartTransition_contDiffAt b x hz hy).restrict_scalars ℝ
  have hfield : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ => P p.2 (chartPt x (chartInv b p.1))) (z,t) :=
    (hP.contDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds
      (show (chartPt x (chartInv b z),t) ∈ Set.univ ×ˢ Set.Ioi 0 from ⟨Set.mem_univ _,ht⟩))).comp (z,t)
      ((hT.comp (z,t) contDiffAt_fst).prodMk contDiffAt_snd)
  have hderiv : ContDiffAt ℝ ∞ (fderiv ℝ (fun y => chartPt x (chartInv b y))) z :=
    hT.fderiv_right (m := ∞) (by simp)
  have hvec (i : Fin k) : ContDiffAt ℝ ∞
      (fun p : ComplexVector n × ℝ => fderiv ℝ (fun y => chartPt x (chartInv b y)) p.1 (realVec (I i))) (z,t) :=
    (hderiv.comp (z,t) contDiffAt_fst).clm_apply contDiffAt_const
  have heval := contDiffAt_alternatingField_apply
    (fun p : ComplexVector n × ℝ => P p.2 (chartPt x (chartInv b p.1)))
    (fun i (p : ComplexVector n × ℝ) => fderiv ℝ (fun y => chartPt x (chartInv b y)) p.1 (realVec (I i)))
    (z,t) hfield hvec
  apply heval.congr_of_eventuallyEq
  have htarget : ∀ᶠ p : ComplexVector n × ℝ in 𝓝 (z,t), p.1 ∈ chartTarget b :=
    continuous_fst.continuousAt.tendsto.eventually ((isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds hz)
  have hsource : ∀ᶠ p : ComplexVector n × ℝ in 𝓝 (z,t),
      chartInv b p.1 ∈ (extChartAt (ComplexModel n) x).source :=
    (hi.tendsto.comp (continuous_fst.tendsto (z,t))).eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hy)
  filter_upwards [htarget,hsource] with p hp hxp
  have hrec : chartForm (chartFormPushforward x (P p.2)) x (chartPt x (chartInv b p.1)) =
      P p.2 (chartPt x (chartInv b p.1)) :=
    chartFormPushforward_to_chart x (P p.2) ((extChartAt (ComplexModel n) x).map_source hxp)
  rw [← chartForm_apply_basis,chartForm_pullback _ b x hp hxp,hrec]
  rfl

theorem regularityChartForm_fiber_eq {A B : RealForm M k} (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (h : chartForm A x (chartPt x y) = chartForm B x (chartPt x y)) : A y = B y := by
  apply ContinuousAlternatingMap.ext
  intro v
  have hh := congrArg (fun Q : HodgeJets.Fiber n k => Q (fun r => tangentCoords x y (v r))) h
  simp only [chartForm,ContinuousAlternatingMap.compContinuousLinearMap_apply,
    chartRealContinuousLinearMap_apply,Function.comp_def] at hh
  have hiy : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
  rw [hiy] at hh
  have heq : (fun r => chartVec x y (tangentCoords x y (v r))) = v :=
    funext fun r => L12Aux.chartVec_tangentCoords x y hy (v r)
  rw [heq] at hh
  exact hh

end Yau.NodeProofs.P06Aux
