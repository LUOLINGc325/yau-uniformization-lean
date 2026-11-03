import Yau.Proofs.P06PDETypeTraceProjection
import Yau.Proofs.P06PDETypeTraceScalarUnique
import Yau.Proofs.P06Geometry

/-! The actual metric trace belongs to the original bounded scalar PDE class. -/
noncomputable section
open Filter MeasureTheory
open scoped Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Aux.PDETypeTrace
open Yau Yau.Blueprint Yau.LeafProofs G04Aux L23Aux L12Aux P06Weitzenbock
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

 def traceCoefficient (g : HermitianField M) (x : M.Carrier)
    (i a b : RIdx n) (z : ComplexVector n) : ℝ :=
  (1 / 2 : ℝ) * (realMetricFn g x z)⁻¹ i a * jMatrix n b i

 theorem trace_components (g : HermitianField M) (A : RealForm M 2)
    (hA : RealOneOne A) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    inChart x (formTrace g A) z = ∑ i, ∑ b, ∑ a,
      traceCoefficient g x i a b z * formComponents A x z ![a,b] := by
  rw [matrixMetricJTrace_form g A hA x hz]
  simp only [matrixMetricJTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul, chartFormMatrix, traceCoefficient]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

 theorem traceCoefficient_smooth (g : SmoothMetric M) (x : M.Carrier) (i a b : RIdx n) :
    ContDiffOn ℝ ∞ (traceCoefficient g.form x i a b) (chartTarget x) := by
  exact (contDiffOn_const.mul (L18Aux.realMetricFn_inverse_contDiffOn g x i a)).mul contDiffOn_const

 theorem trace_smoothTime (g : SmoothMetric M) {U : ℝ → RealForm M 2}
    (hU : SmoothFormTime U (Set.Ioi 0)) (h11 : ∀ t, 0 < t → RealOneOne (U t)) :
    SmoothSpaceTime (fun x t => formTrace g.form (U t) x) (Set.Ioi 0) := by
  intro x
  apply (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun b _ =>
    ContDiffOn.sum (fun a _ =>
      ((traceCoefficient_smooth g x i a b).comp contDiffOn_fst (fun p hp => hp.1)).mul
        (hU x ![a,b]))))).congr
  intro p hp
  exact trace_components g.form (U p.2) (h11 p.2 hp.2) x hp.1

 theorem smallJetsOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set E} (hO : IsOpen O) {f g : ℝ → E → ℝ}
    (hf : SmallJetsOn O f) (hfg : ∀ t, 0 < t → Set.EqOn (f t) (g t) O) :
    SmallJetsOn O g := by
  intro K hK hKO j ε hε
  filter_upwards [hf K hK hKO j ε hε, self_mem_nhdsWithin] with t ht htp
  intro z hz
  have he : f t =ᶠ[𝓝 z] g t :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds (hKO hz)) (hfg t htp)
  rw [← (he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact ht z hz

 theorem trace_initial (g : SmoothMetric M) {A : RealForm M 2} {U : ℝ → RealForm M 2}
    (hA : SmoothRealForm A) (hA11 : RealOneOne A)
    (hU : SmoothFormTime U (Set.Ioi 0)) (h11 : ∀ t, 0 < t → RealOneOne (U t))
    (h0 : FormSmoothInitial U A) :
    ScalarSmoothInitial (fun t => formTrace g.form (U t)) (formTrace g.form A) := by
  rw [scalarSmoothInitial_iff_smallJets]
  refine ⟨by rw [h0.1], ?_⟩
  intro x
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hjet := (formSmoothInitial_iff_smallJets U A).mp h0
  let D := fun (a b : RIdx n) (t : ℝ) (w : ComplexVector n) =>
    formComponents (U t) x w ![a,b] - formComponents A x w ![a,b]
  have hD (a b : RIdx n) (t : ℝ) (ht : 0 < t) : ContDiffOn ℝ ∞ (D a b t) (chartTarget x) :=
    (smoothFormTime_slice hU ht x ![a,b]).sub (hA x ![a,b])
  have hj (i b a : RIdx n) := smallJetsOn_mul hO (hD a b) (hjet.2 x ![a,b])
    (traceCoefficient_smooth g x i a b)
  have hh := smallJetsOn_finset_sum hO Finset.univ _
    (fun i _ t ht => ContDiffOn.sum (fun b _ => ContDiffOn.sum (fun a _ =>
      (traceCoefficient_smooth g x i a b).mul (hD a b t ht))))
    (fun i _ => smallJetsOn_finset_sum hO Finset.univ _
      (fun b _ t ht => ContDiffOn.sum (fun a _ =>
        (traceCoefficient_smooth g x i a b).mul (hD a b t ht)))
      (fun b _ => smallJetsOn_finset_sum hO Finset.univ _
        (fun a _ t ht => (traceCoefficient_smooth g x i a b).mul (hD a b t ht))
        (fun a _ => hj i b a)))
  apply smallJetsOn_congr hO hh
  intro t ht z hz
  change (∑ i, ∑ b, ∑ a, traceCoefficient g.form x i a b z * D a b t z) =
    inChart x (formTrace g.form (U t)) z - inChart x (formTrace g.form A) z
  rw [trace_components g.form (U t) (h11 t ht) x hz, trace_components g.form A hA11 x hz]
  simp only [D, mul_sub, Finset.sum_sub_distrib]

 theorem trace_bounded (g : HermitianField M) {U : ℝ → RealForm M 2}
    (hU : BoundedFormHeatClass g U) (h11 : ∀ t, 0 < t → RealOneOne (U t)) :
    ∀ T, 0 < T → ∃ B : ℝ, 0 < B ∧ ∀ x t, 0 < t → t ≤ T →
      |formTrace g (U t) x| ≤ B := by
  intro T hT
  obtain ⟨B, hB, hb⟩ := hU T hT
  refine ⟨B ^ 2 + (n : ℝ) + 1, by positivity, ?_⟩
  intro x t ht htT
  rw [formTrace_eq_inner_omega g (U t) (h11 t ht)]
  have hh := L03.formInner_abs_le g (U t) (omegaForm g) x
  rw [omegaForm_normSq] at hh
  linarith [hb x t ht htT]

 theorem trace_heatEquation (X : KahlerManifold n) {U : ℝ → RealForm X.manifold 2}
    (hU : SmoothFormTime U (Set.Ioi 0)) (h11 : ∀ t, 0 < t → RealOneOne (U t))
    (hpde : FormHeatEquation X.metric.form U) :
    ∀ x t, 0 < t → HasDerivAt (fun s => formTrace X.metric.form (U s) x)
      (laplacian X.metric.form (formTrace X.metric.form (U t)) x) t := by
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric)
  intro x t ht
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hi : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hUt := smoothFormTime_slice hU ht
  have htr := trace_smooth X.metric.form (L12Aux.metricSmooth_of_smoothMetric X.metric)
    (U t) hUt (h11 t ht)
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    HasDerivAt.fun_sum (fun b (_ : b ∈ Finset.univ) =>
      HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) =>
        (hpde x (chartPt x x) hx t ht ![a,b]).const_mul
          (traceCoefficient X.metric.form x i a b (chartPt x x)))))
  have hH := hodge_oneOne X.metric μ hμ X.kahler_metric (U t) hUt (h11 t ht)
  have htraceH := trace_hodge X.metric μ hμ X.kahler_metric (U t) hUt (h11 t ht)
  have he := congrArg (fun A : RealForm X.manifold 0 => formComponents A x (chartPt x x) Fin.elim0) htraceH
  rw [scalarForm_components] at he
  have hh := hodge_represents X.metric.form (L12Aux.metricSmooth_of_smoothMetric X.metric)
    (scalarForm (formTrace X.metric.form (U t))) (scalarForm_smooth _ htr) x (chartPt x x) hx Fin.elim0
  rw [hh] at he
  change inChart x (formTrace X.metric.form (L03.hodgeRealForm X.metric.form 2 (U t))) (chartPt x x) =
    hodgeComponents X.metric.form x 0
      (fun w (_ : Fin 0 → RIdx n) => inChart x (formTrace X.metric.form (U t)) w)
      (chartPt x x) Fin.elim0 at he
  have hn := (hodgeGeometry X).2.1.1 (formTrace X.metric.form (U t)) htr x (chartPt x x) hx
  have hsum : (∑ i, ∑ b, ∑ a, traceCoefficient X.metric.form x i a b (chartPt x x) *
      hodgeGeneratorComponents X.metric.form x (formComponents (U t) x) (chartPt x x) ![a,b]) =
      laplacian X.metric.form (formTrace X.metric.form (U t)) x := by
    have htc := trace_components X.metric.form (L03.hodgeRealForm X.metric.form 2 (U t)) hH x hx
    simp_rw [hodge_represents X.metric.form (L12Aux.metricSmooth_of_smoothMetric X.metric)
      (U t) hUt x (chartPt x x) hx] at htc
    have he' : formTrace X.metric.form (L03.hodgeRealForm X.metric.form 2 (U t)) x =
        hodgeComponents X.metric.form x 0
          (fun w (_ : Fin 0 → RIdx n) => inChart x (formTrace X.metric.form (U t)) w)
            (chartPt x x) Fin.elim0 := by
      simpa only [inChart, hi, scalarForm_components] using he
    rw [show laplacian X.metric.form (formTrace X.metric.form (U t)) x =
      hodgeGeneratorComponents X.metric.form x
        (fun w (_ : Fin 0 → RIdx n) => inChart x (formTrace X.metric.form (U t)) w)
        (chartPt x x) Fin.elim0 by simpa only [hi] using hn.symm]
    unfold hodgeGeneratorComponents
    rw [← he', show formTrace X.metric.form (L03.hodgeRealForm X.metric.form 2 (U t)) x =
      ∑ i, ∑ b, ∑ a, traceCoefficient X.metric.form x i a b (chartPt x x) *
        hodgeComponents X.metric.form x 2 (formComponents (U t) x) (chartPt x x) ![a,b] by
      simpa only [inChart, hi] using htc]
    simp only [← mul_div_assoc, mul_neg, ← Finset.sum_div, Finset.sum_neg_distrib]
  rw [hsum] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simpa only [inChart, hi] using trace_components X.metric.form (U s) (h11 s hs) x hx

 theorem trace_boundedScalarHeat (X : KahlerManifold n)
    {A : RealForm X.manifold 2} {U : ℝ → RealForm X.manifold 2}
    (hA : BoundedOneOneData X.metric.form A) (hU : IsBoundedFormHeat X.metric.form A U) :
    IsBoundedScalarHeat X.metric.form (formTrace X.metric.form A)
      (fun t => formTrace X.metric.form (U t)) := by
  have h11 := boundedFormHeat_oneOne X A U hA hU
  exact ⟨trace_smoothTime X.metric hU.1 h11, trace_initial X.metric hA.1 hA.2.1 hU.1 h11 hU.2.1,
    trace_bounded X.metric.form hU.2.2.1 h11, trace_heatEquation X hU.1 h11 hU.2.2.2⟩

 theorem hodgeTraceCommutation (X : KahlerManifold n) : HodgeTraceCommutation X.metric.form := by
  intro A U u hA hU hu t ht x
  exact congrFun (boundedScalarHeat_unique X (formTrace X.metric.form A)
    (fun t => formTrace X.metric.form (U t)) u (trace_boundedScalarHeat X hA hU) hu t ht.le) x

end Yau.NodeProofs.P06Aux.PDETypeTrace
