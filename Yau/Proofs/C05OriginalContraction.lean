import Yau.Proofs.C05LoopContractionAssembly
import Yau.Proofs.C05OriginalSpatialMinimum
import Yau.Proofs.C05HessianPropagation

/-! Genuine center Hessian negativity and the original third-jet tube give
one fixed contracting ball, which absorbs every continuous loop. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs
open Yau.Proofs.C05GradientFlowAux Yau.Proofs.C05HessianPropagationAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem simplyConnected_of_original_center_negativity (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : FlowStage X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i) (htwinf : Tendsto tw atTop atTop)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) {a b B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B)
    (hdefect : Tendsto (fun i => scalarHarnackSum h o (tw i) /
      scalarCurvature (h (tw i)) o^2) atTop (𝓝 0))
    (hthird : ∀ᶠ i in atTop, ∀ x ∈ distBall (originalSequenceMetric o h tw hRi i) o (2*b),
      scalarJetNorm (originalSequenceMetric o h tw hRi i)
        (scalarCurvature (originalSequenceMetric o h tw hRi i)) 3 x ≤ B)
    (hcenter : ∀ᶠ i in atTop, ∀ w : TangentVector X.manifold o,
      realHess (originalSequenceMetric o h tw hRi i)
        (scalarCurvature (originalSequenceMetric o h tw hRi i)) o w w ≤
        -(2*a)*realNormSq (originalSequenceMetric o h tw hRi i) o w) :
    SimplyConnectedSpace (Pt X) := by
  let k := originalSequenceMetric o h tw hRi
  let g := fun i => completeRescaledFlowMetric X o h U P ρ hf hH
    (scalarCurvature (h (tw i)) o) (hRi i) (tw i) (htw i)
  let r := min b (a/(2*(B+1)))
  have hr : 0 < r := lt_min hb (by positivity)
  have hrb : r ≤ b := min_le_left _ _
  have hBr : B*(2*r) ≤ a := by
    have H := (le_div_iff₀ (show 0 < 2*(B+1) by positivity)).mp
      (min_le_right b (a/(2*(B+1))))
    change r*(2*(B+1)) ≤ a at H
    nlinarith
  have hgrad : Tendsto (fun i => realNorm (k i) o (realGrad (k i) (scalarCurvature (k i)) o))
      atTop (𝓝 0) := by
    have H := normalized_center_gradient_tendsto_zero o h U P ρ hf.1 hH tw htw hRi hdefect
    change Tendsto (fun i => scalarJetNorm (k i) (scalarCurvature (k i)) 1 o) atTop (𝓝 0) at H
    simpa only [scalarJetNorm_one_eq_realGrad_norm] using H
  have hsmall : ∀ᶠ i in atTop,
      realNorm (k i) o (realGrad (k i) (scalarCurvature (k i)) o) ≤ a*r/8 :=
    (hgrad.eventually (gt_mem_nhds (show (0:ℝ)<a*r/8 by positivity))).mono (fun i hi => hi.le)
  apply C05LoopContractionAssemblyAux.simplyConnected_of_eventual_hessian_bounds
    X o h U P ρ hf hH tw htw htwinf hRi a r ha hr
  filter_upwards [hthird,hcenter,hsmall] with i hTi hCi hGi
  refine ⟨?_,hGi⟩
  intro x hx v
  have hk : MetricSmooth (k i) := L12Aux.metricSmooth_of_smoothMetric (g i)
  have hs : SmoothFn (scalarCurvature (k i)) :=
    scalarCurvature_smoothFn (k i) hk (g i).kahler_equations
  apply realHess_le_neg_on_ball (g i) (scalarCurvature (k i)) hs o hB
    (show 0 < 2*r by positivity) _ hCi hBr x hx v
  intro y hy
  apply hTi y
  exact (L23Aux.mem_distBall_iff (k i) o y (show 0<2*b by positivity)).mpr
    (((L23Aux.mem_distBall_iff (k i) o y (show 0<2*r by positivity)).mp hy).trans_le (by linarith))

end Yau.Proofs.C05Aux
