import Yau.LeafProofs.L16BoundaryChartCover

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance nonlinearChart_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance nonlinearChart_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance nonlinearChart_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance nonlinearChart_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance nonlinearChart_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance nonlinearChart_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance nonlinearChart_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance nonlinearChart_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The complete nonlinear Hessian chain rule includes the first-jet/chart-curvature term. -/
def chartSecondJet {n : ℕ} (L : Space n →L[ℝ] Space n)
    (B : Space n →L[ℝ] Space n →L[ℝ] Space n) (A : Space n →L[ℝ] ℝ)
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  traceHessianPullback L H+((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ) A).comp B

@[simp] theorem chartSecondJet_apply {n : ℕ} (L : Space n →L[ℝ] Space n)
    (B : Space n →L[ℝ] Space n →L[ℝ] Space n) (A : Space n →L[ℝ] ℝ)
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) (v w : Space n) :
    chartSecondJet L B A H v w = H (L v) (L w)+A (B v w) := rfl

/-- Actual second spatial derivatives transform by the complete nonlinear
    chain rule, under only the stated finite differentiability. -/
theorem secondFDeriv_chart_comp {n : ℕ} {f : Space n → Space n} {g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x)) :
    fderiv ℝ (fderiv ℝ (fun y => g (f y))) x = chartSecondJet (fderiv ℝ f x)
      (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ g (f x)) (fderiv ℝ (fderiv ℝ g) (f x)) := by
  have hfD := hf.differentiableAt (by norm_num)
  have hgD := hg.differentiableAt (by norm_num)
  have hffD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hggD := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hProduct := (hggD.hasFDerivAt.comp x hfD.hasFDerivAt).clm_comp hffD.hasFDerivAt
  have hEq : fderiv ℝ (fun y => g (f y)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ g (f y)).comp (fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by norm_num),
      hf.continuousAt.tendsto.eventually (hg.eventually (by norm_num))] with y hfy hgy
    exact fderiv_fun_comp y (hgy.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))
  have h := hEq.fderiv_eq.trans hProduct.fderiv
  convert h using 1
  ext v w
  simp only [chartSecondJet,traceHessianPullback_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,Function.comp_apply,add_comm]

/-- Fixed spatial chart pullback, retaining the real time coordinate. -/
def chartSpaceTimePullback {n : ℕ} (ψ : Space n → Space n) (u : Point n → ℝ) : Point n → ℝ :=
  fun p => u (ψ p.1,p.2)

/-- The actual gradient of a spatial chart pullback. -/
theorem spatialD_chartSpaceTimePullback {n : ℕ} {ψ : Space n → Space n} {u : Point n → ℝ}
    (p : Point n) (hψ : DifferentiableAt ℝ ψ p.1)
    (hu : DifferentiableAt ℝ (fun x => u (x,p.2)) (ψ p.1)) :
    spatialD (chartSpaceTimePullback ψ u) p = (spatialD u (ψ p.1,p.2)).comp (fderiv ℝ ψ p.1) :=
  fderiv_fun_comp p.1 hu hψ

/-- The actual full Hessian of a spatial chart pullback. -/
theorem spatialDD_chartSpaceTimePullback {n : ℕ} {ψ : Space n → Space n} {u : Point n → ℝ}
    (p : Point n) (hψ : ContDiffAt ℝ 2 ψ p.1)
    (hu : ContDiffAt ℝ 2 (fun x => u (x,p.2)) (ψ p.1)) :
    spatialDD (chartSpaceTimePullback ψ u) p = chartSecondJet (fderiv ℝ ψ p.1)
      (fderiv ℝ (fderiv ℝ ψ) p.1) (spatialD u (ψ p.1,p.2)) (spatialDD u (ψ p.1,p.2)) :=
  secondFDeriv_chart_comp hψ hu

/-- Both time fibers are exactly the original closed slab whenever the
    spatial point belongs to the corresponding model and actual domains. -/
theorem timeD_chartSpaceTimePullback {n : ℕ} {S X : Set (Space n)} {T : ℝ}
    (ψ : Space n → Space n) (u : Point n → ℝ) {p : Point n}
    (hp : p.1 ∈ S) (hψp : ψ p.1 ∈ X) :
    timeD (cylinder S 0 T) (chartSpaceTimePullback ψ u) p =
      timeD (cylinder X 0 T) u (ψ p.1,p.2) := by
  simp only [timeD,chartSpaceTimePullback,Parabolic.cylinder,mem_prod,hp,hψp,true_and]

/-- Continuity of the genuine nonlinear second-jet formula follows from
    continuity of its four actual finite jets. -/
theorem chartSecondJet_continuousOn {n : ℕ} {Q : Set (Point n)}
    {L : Point n → Space n →L[ℝ] Space n}
    {B : Point n → Space n →L[ℝ] Space n →L[ℝ] Space n}
    {A : Point n → Space n →L[ℝ] ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hL : ContinuousOn L Q) (hB : ContinuousOn B Q) (hA : ContinuousOn A Q) (hH : ContinuousOn H Q) :
    ContinuousOn (fun p => chartSecondJet (L p) (B p) (A p) (H p)) Q := by
  have hGP := (ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip.continuous.comp_continuousOn hL
  have hT := hGP.clm_comp (hH.clm_comp hL)
  have hC := ((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).continuous.comp_continuousOn hA).clm_comp hB
  exact hT.add hC

/-- A genuine spatial C³ chart transports the frozen parabolic C² structure.
The time variable stays fixed, so no mixed derivative premise is required. -/
theorem c2_chartSpaceTimePullback {n : ℕ} {S X V : Set (Space n)} {T : ℝ}
    (hV : IsOpen V) (hSV : S ⊆ V) {ψ : Space n → Space n}
    (hψ : ContDiffOn ℝ 3 ψ V) (hMapS : MapsTo ψ S X)
    {u : Point n → ℝ} (hu : C2 (cylinder X 0 T) u) :
    C2 (cylinder S 0 T) (chartSpaceTimePullback ψ u) := by
  let Q := cylinder S 0 T
  let Φ : Point n → Point n := fun p => (ψ p.1,p.2)
  have hψAt (p : Point n) (hp : p ∈ Q) : ContDiffAt ℝ 2 ψ p.1 :=
    (hψ.contDiffAt (hV.mem_nhds (hSV hp.1))).of_le (by norm_num)
  have huAt (p : Point n) (hp : p ∈ Q) : ContDiffAt ℝ 2 (fun x => u (x,p.2)) (ψ p.1) :=
    hu.2.2.2.2.1 (ψ p.1,p.2) ⟨hMapS hp.1,hp.2⟩
  have hMap : MapsTo Φ Q (cylinder X 0 T) := fun p hp => ⟨hMapS hp.1,hp.2⟩
  have hΦ : ContinuousOn Φ Q :=
    ((hψ.continuousOn.mono hSV).comp continuous_fst.continuousOn (fun p hp => hp.1)).prodMk
      continuous_snd.continuousOn
  obtain ⟨hDψ,hDDψ,_⟩ := contDiffOn_three_actual_jets_continuous hV hψ
  have hL : ContinuousOn (fun p : Point n => fderiv ℝ ψ p.1) Q :=
    (hDψ.mono hSV).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hB : ContinuousOn (fun p : Point n => fderiv ℝ (fderiv ℝ ψ) p.1) Q :=
    (hDDψ.mono hSV).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hA := hu.2.1.comp hΦ hMap
  have hH := hu.2.2.1.comp hΦ hMap
  refine ⟨hu.1.comp hΦ hMap,?_,?_,?_,?_,?_⟩
  · exact (hA.clm_comp hL).congr (fun p hp => (spatialD_chartSpaceTimePullback p
      ((hψAt p hp).differentiableAt (by norm_num)) ((huAt p hp).differentiableAt (by norm_num))))
  · exact (chartSecondJet_continuousOn hL hB hA hH).congr
      (fun p hp => (spatialDD_chartSpaceTimePullback p (hψAt p hp) (huAt p hp)))
  · exact (hu.2.2.2.1.comp hΦ hMap).congr
      (fun p hp => (timeD_chartSpaceTimePullback ψ u hp.1 (hMapS hp.1)))
  · intro p hp
    exact (huAt p hp).comp p.1 (hψAt p hp)
  · intro p hp
    have hh := hu.2.2.2.2.2 (Φ p) (hMap hp)
    have hX : ψ p.1 ∈ X := hMapS hp.1
    have hS : p.1 ∈ S := hp.1
    simpa only [chartSpaceTimePullback,Φ,Q,Parabolic.cylinder,mem_prod,hX,hS,true_and] using hh

/-- Operator-norm control of the full nonlinear Hessian formula. -/
theorem chartSecondJet_norm_le {n : ℕ} (L : Space n →L[ℝ] Space n)
    (B : Space n →L[ℝ] Space n →L[ℝ] Space n) (A : Space n →L[ℝ] ℝ)
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    ‖chartSecondJet L B A H‖ ≤ ‖L‖^2*‖H‖+‖A‖*‖B‖ := by
  have hG : ‖traceGradientPullback L‖ ≤ ‖L‖ := by
    change ‖(ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip L‖ ≤ ‖L‖
    calc
      _ ≤ ‖(ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip‖*‖L‖ :=
        ContinuousLinearMap.le_opNorm _ L
      _ ≤ 1*‖L‖ := by rw [ContinuousLinearMap.opNorm_flip]; gcongr; exact ContinuousLinearMap.norm_compL_le ℝ (Space n) (Space n) ℝ
      _ = _ := one_mul _
  have hT : ‖traceHessianPullback L H‖ ≤ ‖L‖^2*‖H‖ := by
    change ‖(traceGradientPullback L).comp (H.comp L)‖ ≤ _
    calc
      _ ≤ ‖traceGradientPullback L‖*‖H.comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L‖*(‖H‖*‖L‖) := mul_le_mul hG (H.opNorm_comp_le L) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hC : ‖((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ) A).comp B‖ ≤ ‖A‖*‖B‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact ((ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).le_opNorm A).trans
      (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_compL_le ℝ (Space n) (Space n) ℝ))
  exact (norm_add_le _ _).trans (add_le_add hT hC)

/-- The sup portions of the original Schauder estimate and the actual chart
    jet bounds give all four raw parabolic jet bounds with a linear data budget. -/
theorem schauder_chart_raw_jet_bound {n : ℕ} {S X V : Set (Space n)} {T α P C : ℝ}
    (hV : IsOpen V) (hSV : S ⊆ V) {ψ : Space n → Space n}
    (hψ : ContDiffOn ℝ 3 ψ V) (hMapS : MapsTo ψ S X)
    (hChart : ∀ x ∈ S, ‖fderiv ℝ ψ x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ C)
    {u : Point n → ℝ} (hu : SchauderBound α (cylinder X 0 T) u P)
    {p : Point n} (hp : p ∈ cylinder S 0 T) :
    |chartSpaceTimePullback ψ u p| ≤ P ∧
      ‖spatialD (chartSpaceTimePullback ψ u) p‖ ≤ C*P ∧
      ‖spatialDD (chartSpaceTimePullback ψ u) p‖ ≤ (C^2+C)*P ∧
      |timeD (cylinder S 0 T) (chartSpaceTimePullback ψ u) p| ≤ P := by
  have hActual : (ψ p.1,p.2) ∈ cylinder X 0 T := ⟨hMapS hp.1,hp.2⟩
  have hψAt : ContDiffAt ℝ 2 ψ p.1 :=
    (hψ.contDiffAt (hV.mem_nhds (hSV hp.1))).of_le (by norm_num)
  have huAt := hu.1.2.2.2.2.1 (ψ p.1,p.2) hActual
  have hLow := hu.2.2.1 (ψ p.1,p.2) hActual
  have hH : ‖spatialDD u (ψ p.1,p.2)‖ ≤ P := hu.2.2.2.1.2.1 _ hActual
  have hTime : ‖timeD (cylinder X 0 T) u (ψ p.1,p.2)‖ ≤ P := hu.2.2.2.2.2.1 _ hActual
  obtain ⟨hL,hB⟩ := hChart p.1 hp.1
  refine ⟨hLow.1,?_,?_,?_⟩
  · rw [spatialD_chartSpaceTimePullback p (hψAt.differentiableAt (by norm_num))
      (huAt.differentiableAt (by norm_num))]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hLow.2 hL (norm_nonneg _) hu.2.1)).trans_eq (mul_comm _ _)
  · rw [spatialDD_chartSpaceTimePullback p hψAt huAt]
    apply (chartSecondJet_norm_le _ _ _ _).trans
    calc
      _ ≤ C^2*P+P*C := add_le_add
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hL 2) hH (norm_nonneg _) (sq_nonneg C))
        (mul_le_mul hLow.2 hB (norm_nonneg _) hu.2.1)
      _ = _ := by ring
  · rw [timeD_chartSpaceTimePullback ψ u hp.1 (hMapS hp.1)]
    exact hTime

end Yau.LeafProofs.L16Aux
