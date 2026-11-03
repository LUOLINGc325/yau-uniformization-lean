import Yau.Proofs.C05GradientFlow
import Yau.Proofs.C05LoopIngress
import Yau.Proofs.C05CompleteFlowMetric
import Yau.Proofs.C05ScalarTimeSourceBoundsSmooth

/-! Actual good-time loop ingress and the genuine gradient contraction imply simple connectivity. -/
noncomputable section
open Filter
open scoped Topology Manifold unitInterval
namespace Yau.Proofs.C05LoopContractionAssemblyAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
open Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem loop_nullhomotopic_of_eventual_hessian_bounds
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i) (htwinf : Tendsto tw atTop atTop)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) (a r : ℝ)
    (ha : 0 < a) (hr : 0 < r)
    (hbounds : ∀ᶠ i in atTop,
      let k := scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))
      (∀ x ∈ distBall k o (2*r), ∀ v : TangentVector X.manifold x,
        realHess k (scalarCurvature k) x v v ≤ -a*realNormSq k x v) ∧
      realNorm k o (realGrad k (scalarCurvature k) o) ≤ a*r/8)
    (x : Pt X) (γ : Path x x) : γ.Homotopic (Path.refl x) := by
  have hingress := C05LoopIngressAux.loop_eventually_mem_rescaled_ball X o h U P ρ
    hf.1 hH tw htw htwinf hRi x γ (r/2) (by positivity)
  obtain ⟨i,hi,hγ⟩ := (hbounds.and hingress).exists
  let g := completeRescaledFlowMetric X o h U P ρ hf hH
    (scalarCurvature (h (tw i)) o) (hRi i) (tw i) (htw i)
  have hfi : SmoothFn (scalarCurvature g.form) :=
    C05ScalarTimeSourceBoundsAux.scalarCurvature_smoothFn g.form
      (metricSmooth_of_smoothMetric g) g.kahler_equations
  apply loop_nullhomotopic_of_hessian_negative g (scalarCurvature g.form) hfi
    o a r ha hr hi.1 hi.2 γ
  intro u
  change inducedDistance g.form o (γ u) ≤ r/2
  exact ((mem_distBall_iff g o (γ u) (by positivity)).mp (hγ u)).le

theorem simplyConnected_of_eventual_hessian_bounds
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i) (htwinf : Tendsto tw atTop atTop)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) (a r : ℝ)
    (ha : 0 < a) (hr : 0 < r)
    (hbounds : ∀ᶠ i in atTop,
      let k := scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))
      (∀ x ∈ distBall k o (2*r), ∀ v : TangentVector X.manifold x,
        realHess k (scalarCurvature k) x v v ≤ -a*realNormSq k x v) ∧
      realNorm k o (realGrad k (scalarCurvature k) o) ≤ a*r/8) :
    SimplyConnectedSpace (Pt X) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨?_,fun x γ => loop_nullhomotopic_of_eventual_hessian_bounds
    X o h U P ρ hf hH tw htw htwinf hRi a r ha hr hbounds x γ⟩
  refine ⟨⟨o⟩,?_⟩
  intro x y
  obtain ⟨δ⟩ := X.metric.curve_nonempty x y
  exact ⟨{
    toFun := fun u => δ u
    continuous_toFun := δ.continuous_on.comp_continuous continuous_subtype_val (fun u => u.2)
    source' := δ.start_eq
    target' := δ.finish_eq }⟩

end Yau.Proofs.C05LoopContractionAssemblyAux
