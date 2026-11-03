import Yau.LeafProofs.L03
import Yau.LeafProofs.L23JetNaturality
import Yau.LeafProofs.L23TensorTraceFrame
import Yau.Blueprint.HodgeContracts

noncomputable section
open scoped Manifold Topology ContDiff Matrix
open Filter
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

theorem form_tensorEval (A : RealForm M k) (x : M.Carrier) (z : ComplexVector n) :
    L23Aux.tensorEvalCLM (formComponents A x z) =
      (L03.chartForm A x z).toContinuousMultilinearMap :=
  L23Aux.tensorEvalCLM_coefficients (L03.chartForm A x z).toContinuousMultilinearMap

theorem covariantD_form_cons (h : HermitianField M) (A : RealForm M k)
    (x : M.Carrier) (z : ComplexVector n) (a : RIdx n) (I : Fin k → RIdx n) :
    covariantD h x (formComponents A x) z (Fin.cons a I) =
      covariantComponents h x (formComponents A x) z a I := by
  simp only [covariantD, Fin.cons_zero, Fin.cons_succ, covariantComponents]

theorem covariantD_form_chart_change (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M k) (hA : SmoothRealForm A) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    covariantD h c (formComponents A c) z =
      L23Aux.tensorFrameTransform (L23Aux.realChartJacobian c d z)
        (covariantD h d (formComponents A d) (L12Aux.realChartChange c d z)) := by
  apply L23Aux.tensorEvalCLM_injective
  rw [L23Aux.realChartJacobian, L23Aux.tensorEvalCLM_frameTransform]
  apply L23Aux.covariantD_chart_change h hs c d (formComponents A c) (formComponents A d) hz hy
  · intro I
    exact ((hA c I).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  · intro I
    have hd : L12Aux.realChartChange c d z ∈ chartTarget d :=
      (extChartAt (ComplexModel n) d).map_source hy
    exact ((hA d I).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) d).mem_nhds hd)).differentiableAt (by simp)
  · intro w hw
    rw [form_tensorEval, form_tensorEval]
    exact congrArg ContinuousAlternatingMap.toContinuousMultilinearMap
      (L03.chartForm_pullback A c d hw.1 hw.2)

theorem codifferential_tensor_trace (h : HermitianField M) (A : RealForm M (k + 1))
    (c : M.Carrier) (z : ComplexVector n) :
    codifferentialComponents h c (formComponents A c) z =
      -L23Aux.tensorMetricTrace (realMetricFn h c z)⁻¹
        (covariantD h c (formComponents A c) z) := by
  funext I
  simp only [codifferentialComponents, Pi.neg_apply, L23Aux.tensorMetricTrace,
    covariantD_form_cons]

theorem codifferential_form_chart_change (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    codifferentialComponents h c (formComponents A c) z =
      L23Aux.tensorFrameTransform (L23Aux.realChartJacobian c d z)
        (codifferentialComponents h d (formComponents A d)
          (L12Aux.realChartChange c d z)) := by
  rw [codifferential_tensor_trace, codifferential_tensor_trace,
    covariantD_form_chart_change h hs A hA c d hz hy,
    L23Aux.tensorMetricTrace_frameTransform,
    L23Aux.inverseMetric_chart_change h c d hz hy]
  funext I
  simp only [Pi.neg_apply, L23Aux.tensorFrameTransform, neg_mul, Finset.sum_neg_distrib]

theorem codifferentialChartForm_tensorEval (h : HermitianField M)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    L23Aux.tensorEvalCLM (codifferentialComponents h c (formComponents A c) z) =
      (L03.codifferentialChartForm h A c z).toContinuousMultilinearMap := by
  have he := L23Aux.tensorEvalCLM_coefficients
    (L03.codifferentialChartForm h A c z).toContinuousMultilinearMap
  simpa only [ContinuousAlternatingMap.coe_toContinuousMultilinearMap,
    L03.codifferentialChartForm_coeff h A hA c hz] using he

theorem codifferentialChartForm_pullback (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    L03.codifferentialChartForm h A c z =
      (L03.codifferentialChartForm h A d (L12Aux.realChartChange c d z)).compContinuousLinearMap
        (fderiv ℝ (L12Aux.realChartChange c d) z) := by
  have hd : L12Aux.realChartChange c d z ∈ chartTarget d :=
    (extChartAt (ComplexModel n) d).map_source hy
  have he := congrArg L23Aux.tensorEvalCLM
    (codifferential_form_chart_change h hs A hA c d hz hy)
  rw [codifferentialChartForm_tensorEval h A hA c hz, L23Aux.realChartJacobian,
    L23Aux.tensorEvalCLM_frameTransform, codifferentialChartForm_tensorEval h A hA d hd] at he
  apply ContinuousAlternatingMap.ext
  intro V
  exact congrArg (fun T : L23Aux.RealTensorForm n k => T V) he

theorem codifferentialRealForm_eq_chart (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (c y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) c).source) :
    L03.codifferentialRealForm h A y = L03.chartCodifferentialRealForm h A c y := by
  have hcenter : chartInv c (chartPt c y) = y :=
    (extChartAt (ComplexModel n) c).left_inv hy
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hy
  have hn : chartInv c (chartPt c y) ∈ (extChartAt (ComplexModel n) y).source := by
    rw [hcenter]
    exact mem_extChartAt_source y
  have he := codifferentialChartForm_pullback h hs A hA c y hz hn
  apply ContinuousAlternatingMap.ext
  intro V
  have hv := congrArg (fun P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ =>
    P (fun i => tangentCoords c y (V i))) he
  have htrans (v : TangentVector M y) :
      fderiv ℝ (L12Aux.realChartChange c y) (chartPt c y) (tangentCoords c y v) =
        tangentCoords y y v := by
    change fderiv ℝ (fun t => chartPt y (chartInv c t)) (chartPt c y) _ = _
    rw [L03.chartTransition_real_fderiv c y hz hn]
    rw [hcenter, L12Aux.chartVec_tangentCoords c y hy]
  simpa only [L03.codifferentialRealForm, L03.chartCodifferentialRealForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    L03.tangentCoordsRealContinuousLinearMap_apply, L12Aux.realChartChange,
    hcenter, htrans] using hv.symm

theorem codifferential_represents (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) :
    RepresentsCodifferential h A (L03.codifferentialRealForm h A) := by
  intro x z hz I
  have hv := codifferentialRealForm_eq_chart h hs A hA x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz)
  have hc : formComponents (L03.codifferentialRealForm h A) x z I =
      formComponents (L03.chartCodifferentialRealForm h A x) x z I := by
    unfold formComponents
    rw [hv]
  exact hc.trans (L03.chartCodifferentialRealForm_coeff h A hA x hz I)

theorem covariantComponents_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (F : FormComponents n k)
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (a : RIdx n) (I : Fin k → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => covariantComponents h x F z a I) (chartTarget x) := by
  apply (L12Aux.rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x) (hF I) a).sub
  apply ContDiffOn.sum
  intro r _
  apply ContDiffOn.sum
  intro c _
  exact (L23Aux.christoffel_contDiffOn h hs x c a (I r)).mul (hF (Function.update I r c))

theorem codifferentialComponents_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (F : FormComponents n (k + 1))
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x)) (I : Fin k → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => codifferentialComponents h x F z I) (chartTarget x) := by
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact (L23Aux.realMetricFn_inverse_contDiffOn h hs x a b).mul
    (covariantComponents_smooth h hs x F hF a (Fin.cons b I))

theorem codifferential_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) :
    SmoothRealForm (L03.codifferentialRealForm h A) := by
  intro x I
  apply (codifferentialComponents_smooth h hs x (formComponents A x) (hA x) I).congr
  intro z hz
  exact codifferential_represents h hs A hA x z hz I

theorem hodge_represents (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M k) (hA : SmoothRealForm A) :
    RepresentsHodge h A (L03.hodgeRealForm h k A) := by
  cases k with
  | zero =>
      have hAd := L03.exteriorRealForm_represents A hA
      have hδd := codifferential_represents h hs (L03.exteriorRealForm A)
        (L03.exteriorRealForm_smooth A hA)
      intro x z hz I
      change formComponents (L03.codifferentialRealForm h (L03.exteriorRealForm A)) x z I =
        codifferentialComponents h x (exteriorComponents (formComponents A x)) z I
      rw [hδd x z hz I]
      exact congrFun (L03.codifferentialComponents_congr_nhds h x
        (L03.representsExterior_components_eventuallyEq hAd x hz)) I
  | succ j =>
      have hδA := codifferential_represents h hs A hA
      have hdA := L03.exteriorRealForm_represents A hA
      have hdδ := L03.exteriorRealForm_represents (L03.codifferentialRealForm h A)
        (codifferential_smooth h hs A hA)
      have hδd := codifferential_represents h hs (L03.exteriorRealForm A)
        (L03.exteriorRealForm_smooth A hA)
      intro x z hz I
      change formComponents (L03.exteriorRealForm (L03.codifferentialRealForm h A) +
        L03.codifferentialRealForm h (L03.exteriorRealForm A)) x z I =
        exteriorComponents (codifferentialComponents h x (formComponents A x)) z I +
          codifferentialComponents h x (exteriorComponents (formComponents A x)) z I
      simp only [L03.formComponents_add, Pi.add_apply]
      rw [hdδ x z hz I, hδd x z hz I]
      rw [congrFun (L03.exteriorComponents_congr_nhds
        (L03.representsCodifferential_components_eventuallyEq h hδA x hz)) I,
        congrFun (L03.codifferentialComponents_congr_nhds h x
          (L03.representsExterior_components_eventuallyEq hdA x hz)) I]

theorem hodge_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M k) (hA : SmoothRealForm A) : SmoothRealForm (L03.hodgeRealForm h k A) := by
  cases k with
  | zero => exact codifferential_smooth h hs _ (L03.exteriorRealForm_smooth A hA)
  | succ j =>
      exact L03.smoothRealForm_add _ _
        (L03.exteriorRealForm_smooth _ (codifferential_smooth h hs A hA))
        (codifferential_smooth h hs _ (L03.exteriorRealForm_smooth A hA))

theorem formCalculus (h : HermitianField M) (hs : MetricSmooth h) : FormCalculusRealization h := by
  refine ⟨?_, ?_, ?_⟩
  · intro k A hA
    exact ⟨L03.exteriorRealForm A, L03.exteriorRealForm_smooth A hA,
      L03.exteriorRealForm_represents A hA⟩
  · intro k A hA
    exact ⟨L03.codifferentialRealForm h A, codifferential_smooth h hs A hA,
      codifferential_represents h hs A hA⟩
  · intro k A hA
    exact ⟨L03.hodgeRealForm h k A, hodge_smooth h hs A hA, hodge_represents h hs A hA⟩

end Yau.NodeProofs.G04Aux
