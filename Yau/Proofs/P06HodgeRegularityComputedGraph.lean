import Yau.Proofs.P06HodgeRegularityHodgeForward

/-! Smooth actual entries in the original closed Hodge graph satisfy the
original computed □ equation at every point of every chart. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α]

theorem regularityForwardPrincipal_contDiff
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (r : α) :
    ContDiff ℝ ∞ (fun z => hodgeForwardPrincipal v a e1 e0 U z r) :=
  ContDiff.sum fun c _ => ((ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (ha r c i j).mul (regularityDirection_contDiff (regularityDirection_contDiff (hU c) (v j)) (v i))).neg.add
    (ContDiff.sum fun i _ => (he1 r c i).mul (regularityDirection_contDiff (hU c) (v i)))).add
      ((he0 r c).mul (hU c))

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeClosureGraph_smooth_represents
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : RealForm M k) (hA : SmoothRealForm A) (hW : SmoothRealForm W)
    (hAL : L2RealForm g.form μ A) (hWL : L2RealForm g.form μ W)
    (hgraph : (realizeActualForm g μ A hAL,realizeActualForm g μ W hWL) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph) : RepresentsHodge g.form A W := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  intro x z hz I
  have hChart : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  obtain ⟨V,hV,hzV,hVO,hcV⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := z)) hChart (Set.singleton_subset_iff.mpr hz)
  obtain ⟨θ,hθ,hcθ,hθO,_,hθone⟩ := exists_model_chart_cutoff hChart hcV hVO
  have hone y (hy : y ∈ V) : θ y = 1 := (hθone y (subset_closure hy)).1
  have hzV' : z ∈ V := hzV (Set.mem_singleton _)
  let b := Module.finBasis ℝ (HodgeJets.Fiber n k)
  let q := fun i j y => θ y * hodgeRegularityQ g.form x i j y
  let E1 := fun r c i y => θ y * hodgeRegularityE1 g.form x b r c i y
  let E0 := fun r c y => θ y * hodgeRegularityE0 g.form x b r c y
  let U := hodgeRegularityChartInput x b θ A
  let W0 := hodgeRegularityChartInput x b θ W
  have hq i j := (scalar_cutoff_contDiff_properties hChart θ hθ hcθ hθO _ (hodgeRegularityQ_contDiffOn g x i j)).1
  have hE1 r c i := (scalar_cutoff_contDiff_properties hChart θ hθ hcθ hθO _ (hodgeRegularityE1_contDiffOn g x b r c i)).1
  have hE0 r c := (scalar_cutoff_contDiff_properties hChart θ hθ hcθ hθO _ (hodgeRegularityE0_contDiffOn g x b r c)).1
  have hU c := hodgeRegularityChartInput_contDiff x b θ hθ hcθ hθO A hA c
  have hW0 r := hodgeRegularityChartInput_contDiff x b θ hθ hcθ hθO W hW r
  have hUL c : MemLp (fun y => U y c) 2 (lebesgueC n) :=
    chartFunctional_memLp g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap A hAL
  have ha := regularityScalarSystemA_contDiff (α := Fin (finrank ℝ (HodgeJets.Fiber n k))) q hq
  have hweak := hodgeClosureGraph_cutoff_forwardWeak g μ hμ A W hAL hWL hgraph x b θ hθ hcθ hθO
    hV (subset_closure.trans hVO) hone
  have hcoord (r : Fin (finrank ℝ (HodgeJets.Fiber n k))) :
      hodgeRegularityCoord b W x z r = hodgeRegularityCoord b (hodgeRealForm g.form k A) x z r := by
    let F := fun y => hodgeForwardPrincipal (realModelBasis n) (regularityScalarSystemA q) E1 E0 U y r
    have hF : ContDiff ℝ ∞ F := regularityForwardPrincipal_contDiff _ _ _ _ U ha hE1 hE0 hU r
    have hzero : F z - W0 z r = 0 := eq_zero_of_smooth_integral_tests (lebesgueC n) hV
      (fun y => F y - W0 y r) ((hF.sub (hW0 r)).contDiffOn) (fun φ hφ hcφ hφV => by
        have htφ : regularityTest V φ := ⟨hφ,hcφ,hφV⟩
        have hh := hweak r φ htφ
        rw [regularityForwardTranspose_integral_restrict (lebesgueC n) _ _ E1 E0 ha hE1 hE0 htφ U r,
          regularityForwardSource_integral_restrict (lebesgueC n) htφ (fun y => W0 y r),
          regularitySmoothTranspose_principal (lebesgueC n) _ _ E1 E0 ha hE1 hE0 U hU hUL hφ hcφ r] at hh
        have hFI : Integrable (fun y => φ y * F y) (lebesgueC n) :=
          (hφ.continuous.mul hF.continuous).integrable_of_hasCompactSupport hcφ.mul_right
        have hWI : Integrable (fun y => φ y * W0 y r) (lebesgueC n) :=
          (hφ.continuous.mul (hW0 r).continuous).integrable_of_hasCompactSupport hcφ.mul_right
        simp only [smul_eq_mul,mul_sub]
        rw [integral_sub hFI hWI,hh,sub_self]) hzV'
    have hcalc := hodgeRegularity_chart_cutoff_source g μ hμ x b θ θ hθ hcθ hθO hθ hcθ hθO
      hV (subset_closure.trans hVO) hone hone A hA hzV' r
    rw [regularityScalarSystem_eq_forwardPrincipal (realModelBasis n) q E1 E0 U hq hE1 hU z r] at hcalc
    have hWval : W0 z r = hodgeRegularityCoord b W x z r := by simp only [W0,hodgeRegularityChartInput,hone z hzV',one_mul]
    exact hWval.symm.trans ((sub_eq_zero.mp hzero).symm.trans hcalc)
  have hfields : chartForm W x z = chartForm (hodgeRealForm g.form k A) x z :=
    b.repr.injective (Finsupp.ext fun r => hcoord r)
  exact (congrArg (fun Q : HodgeJets.Fiber n k => Q (fun r => realVec (I r))) hfields).trans
    (hodgeRealForm_represents g μ hμ A hA x z hz I)

end Yau.NodeProofs.P06Aux
