import Yau.Proofs.C05LoopIngressCompactCurves
import Yau.Proofs.C05LoopIngressMetricDecay
import Yau.Proofs.C07CurveLength

/-! The same bounded original curves control the actual rescaled distances uniformly on the loop. -/
noncomputable section
open Filter
open scoped Topology Manifold unitInterval
namespace Yau.Proofs.C05LoopIngressAux
open Yau Yau.Blueprint
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1200000

theorem eventually_uniform_loop_distance_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (tw : ℕ → ℝ)
    (htw : ∀ i, 0 < tw i) (htwinf : Tendsto tw atTop atTop)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o)
    (x : Pt X) (γ : Path x x) :
    ∃ B a L : ℝ, 0 < B ∧ 0 < a ∧ 0 ≤ L ∧
      ∀ᶠ i in atTop, ∀ u : I,
        inducedDistance (scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))) o (γ u) ≤
          Real.sqrt (B * tw i ^ (-a)) * L := by
  have hg₀ : MetricSmooth X.metric.form := by
    have H := C04Aux.localizedFlow_metricSmooth X o h U P ρ hf (t := 0) (by norm_num)
    rwa [hf.1.1] at H
  obtain ⟨K, L, hK, hL, hcurves⟩ := exists_uniform_loop_curve_family X.metric hg₀ o x γ
  obtain ⟨B, a, hB, ha, horder⟩ := rescaled_metric_order_on_compact X o h hH K hK
  refine ⟨B, a, L, hB, ha, hL, ?_⟩
  filter_upwards [htwinf.eventually (eventually_ge_atTop (1 : ℝ))] with i hi
  intro u
  obtain ⟨η, hηlen, hηK⟩ := hcurves u
  let k := scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))
  have hk : MetricSmooth k := C04RescaledTubeAux.metricSmooth_scale _ (hRi i) _
    (C04Aux.localizedFlow_metricSmooth X o h U P ρ hf (htw i).le)
  have hA : 0 ≤ B * tw i ^ (-a) := mul_nonneg hB.le (Real.rpow_nonneg (htw i).le _)
  have H := C07CurveLengthAux.curve_length_comparison hk η hA
    (fun s hs => horder (tw i) hi (hRi i) (η.1 s) (hηK s hs))
  let ηnew : IntegrableCurve k o (γ u) := ⟨η.1, H.1⟩
  exact (Yau.LeafProofs.L12Aux.inducedDistance_le_curveLength k ηnew).trans
    (H.2.trans (mul_le_mul_of_nonneg_left hηlen (Real.sqrt_nonneg _)))

end Yau.Proofs.C05LoopIngressAux
