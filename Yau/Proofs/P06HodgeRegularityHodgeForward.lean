import Yau.Proofs.P06HodgeRegularityStrongForward
import Yau.Proofs.P06HodgeRegularityScalarForward
import Yau.Proofs.P06HodgeRegularityChartCutoff
import Yau.Proofs.P06ChartProjectionStrong

/-! Every original closed Hodge graph edge solves the actual local
forward distributional system. Each edge uses its own genuine core sequence. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeClosureGraph_cutoff_forwardWeak {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : RealForm M k) (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W)
    (hgraph : (realizeActualForm g μ A hA, realizeActualForm g μ W hW) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (θ : ComplexVector n → ℝ) (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ)
    (hθO : tsupport θ ⊆ chartTarget x)
    {V : Set (ComplexVector n)} (hV : IsOpen V) (hVO : V ⊆ chartTarget x)
    (hθone : ∀ z ∈ V, θ z = 1) :
    regularityForwardWeak (lebesgueC n) V (realModelBasis n)
      (fun i j z => θ z * hodgeRegularityQ g.form x i j z)
      (fun r c i z => θ z * hodgeRegularityE1 g.form x b r c i z)
      (fun r c z => θ z * hodgeRegularityE0 g.form x b r c z)
      (hodgeRegularityChartInput x b θ A) (hodgeRegularityChartInput x b θ W) := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  let qe := fun i j z => θ z * hodgeRegularityQ g.form x i j z
  let E1 := fun r c i z => θ z * hodgeRegularityE1 g.form x b r c i z
  let E0 := fun r c z => θ z * hodgeRegularityE0 g.form x b r c z
  have hq (i j : RIdx n) : ContDiff ℝ ∞ (qe i j) :=
    (scalar_cutoff_contDiff_properties hO θ hθ hcθ hθO _ (hodgeRegularityQ_contDiffOn g x i j)).1
  have hE1 (r c : α) (i : RIdx n) : ContDiff ℝ ∞ (E1 r c i) :=
    (scalar_cutoff_contDiff_properties hO θ hθ hcθ hθO _ (hodgeRegularityE1_contDiffOn g x b r c i)).1
  have hE0 (r c : α) : ContDiff ℝ ∞ (E0 r c) :=
    (scalar_cutoff_contDiff_properties hO θ hθ hcθ hθO _ (hodgeRegularityE0_contDiffOn g x b r c)).1
  obtain ⟨As,Ws,hcore,hAs,hWs⟩ := hodgeClosureGraph_core_approximation g μ hμ A W hA hW hgraph
  let Us := fun m => hodgeRegularityChartInput x b θ (As m)
  let Vs := fun m => hodgeRegularityChartInput x b θ (Ws m)
  let U := hodgeRegularityChartInput x b θ A
  let W0 := hodgeRegularityChartInput x b θ W
  have hUs (m : ℕ) (c : α) := hodgeRegularityChartInput_contDiff x b θ hθ hcθ hθO (As m) (hcore m).1 c
  have hUsL (m : ℕ) (c : α) : MemLp (fun z => Us m z c) 2 (lebesgueC n) :=
    chartFunctional_memLp g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap (As m) (hcore m).2.2.2.1
  have hVsL (m : ℕ) (c : α) : MemLp (fun z => Vs m z c) 2 (lebesgueC n) :=
    chartFunctional_memLp g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap (Ws m) (hcore m).2.2.2.2.1
  have hUL (c : α) : MemLp (fun z => U z c) 2 (lebesgueC n) :=
    chartFunctional_memLp g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap A hA
  have hWL (c : α) : MemLp (fun z => W0 z c) 2 (lebesgueC n) :=
    chartFunctional_memLp g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap W hW
  have hUt (c : α) : Tendsto (fun m => ∫ z, ‖Us m z c - U z c‖^2 ∂lebesgueC n) atTop (𝓝 0) := by
    have hp := chartFunctional_strong_l2_tendsto g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap
      As A (fun m => (hcore m).2.2.2.1) hA hAs
    simpa only [Us,U,hodgeRegularityChartInput,hodgeRegularityCoord,
      LinearMap.coe_toContinuousLinearMap',Basis.coord_apply,Real.norm_eq_abs,sq_abs,mul_sub] using hp
  have hWt (c : α) : Tendsto (fun m => ∫ z, ‖Vs m z c - W0 z c‖^2 ∂lebesgueC n) atTop (𝓝 0) := by
    have hp := chartFunctional_strong_l2_tendsto g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap
      Ws W (fun m => (hcore m).2.2.2.2.1) hW hWs
    simpa only [Vs,W0,hodgeRegularityChartInput,hodgeRegularityCoord,
      LinearMap.coe_toContinuousLinearMap',Basis.coord_apply,Real.norm_eq_abs,sq_abs,mul_sub] using hp
  apply regularityForwardWeak_of_strong_smooth (lebesgueC n) (realModelBasis n) qe E1 E0
    hq hE1 hE0 Us Vs U W0 hUs hUsL hVsL hUL hWL hUt hWt
  intro m z hz r
  rw [← regularityScalarSystem_eq_forwardPrincipal (realModelBasis n) qe E1 E0 (Us m) hq hE1 (hUs m) z r]
  have hs := hodgeRegularity_chart_cutoff_source g μ hμ x b θ θ hθ hcθ hθO hθ hcθ hθO
    hV hVO hθone hθone (As m) (hcore m).1 hz r
  change _ = θ z * hodgeRegularityCoord b (Ws m) x z r
  rw [hθone z hz,one_mul,(hodgeCorePair_iff_computed g μ hμ (As m) (Ws m)).mp (hcore m) |>.2.2]
  exact hs

end Yau.NodeProofs.P06Aux
