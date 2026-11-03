import Yau.Proofs.C04BoundedGeometryChartsUniformCoordinateJets
import Yau.Proofs.C04BoundedGeometryChartsUnitaryChart
import Yau.Proofs.C04BoundedGeometryChartsMetricEntryJets
import Yau.Proofs.C04PullbackModelJets

/-! Uniform actual holomorphic charts from intrinsic bounds for all curvature jets. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem quantitativeHolomorphicCharts (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ℝ) (hK : ∀ m, 0 < K m) :
    ∃ rc c C : ℝ, 0 < rc ∧ 0 < c ∧ 0 < C ∧
      ∃ Cm : ℕ → ℝ, (∀ m, 0 < Cm m) ∧
        ∀ (M : ComplexManifold n) (k : HermitianField M) (p : M.Carrier),
          MetricSmooth k → KahlerClosed k → IsCompleteDistance (lengthDist k) →
          (∀ m x, x ∈ distBall k p (2 * r) → curvatureJetNorm k m x ≤ K m) →
          ∃ Phi : ComplexVector n → M.Carrier,
            UnitaryChart k p Phi rc c C ∧
              ∀ m, PullbackDerivBound k Phi (rc / 2) m (Cm m) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨R, hR, B, hB, d, hd, hd1, hdR, D, hD, hcoordinates⟩ :=
    exists_uniform_normal_coordinate_jet_bounds n hn r K hr hK
  obtain ⟨P, hP, hinverse⟩ := exists_uniform_inverse_of_coordinate_function (E := ComplexVector n) D hD
  obtain ⟨Hbound, hHbound, hmodel⟩ := C04Aux.exists_pullback_model_jet_bounds
    (E := ComplexVector n) R d hR hd hd1 hdR B P hB hP
  refine ⟨d / 16, 1 / 16, 16, by positivity, by norm_num, by norm_num,
    gramDerivativeBudget n Hbound, fun m => gramDerivativeBudget_pos Hbound hHbound m, ?_⟩
  intro M k p hks hkahler hcomplete hcurv
  let g := smoothMetric_of_complete_field k hks hkahler hcomplete
  obtain ⟨U, hU⟩ := exists_complex_unitary_frame g.form p
  obtain ⟨hseed, hjet, F, hF, hF0, hclose, hcomplex, hFjet⟩ :=
    hcoordinates M g hkahler p U hU hcurv
  obtain ⟨e, he, hs, ht, he0, heSmooth, heNorm, heJets⟩ := hinverse F hF hF0 hclose hFjet
  let L := fderiv ℝ F 0
  let Phi := normalChartMap g p U e L d
  have hL : ‖L‖ ≤ (5 / 4 : ℝ) := coordinate_fderiv_zero_norm F
    (hclose 0 (Metric.mem_ball_self (by norm_num)))
  have h8 : Metric.ball (0 : ComplexVector n) (1 / 8 : ℝ) ⊆ e.target := by
    intro w hw
    exact ht (Metric.closedBall_subset_closedBall (by norm_num : (1 / 8 : ℝ) ≤ 3 / 16)
      (Metric.ball_subset_closedBall hw))
  have hunit : UnitaryChart g.form p Phi (d / 16) (1 / 16) 16 :=
    normalChartMap_unitary g hkahler p U hU R hR d hd hdR
      (fun y hy => (hseed y hy).2.1) (fun y hy => (hseed y hy).2.2)
      F hF hclose hcomplex e he hs ht he0 heSmooth heNorm
  have hHm := hmodel (radialCoframe g p U) e.symm L (radialCoframe_smooth g p U)
    (fun m x hx => (hjet m x (Metric.ball_subset_closedBall hx)).1)
    (heSmooth.mono h8) heJets (fun w hw => heNorm w (h8 hw)) hL
  have heqModel : C04Aux.pullbackModelMetric d (radialCoframe g p U) e.symm L =
      normalChartGram g p U e L d := rfl
  rw [heqModel] at hHm
  obtain ⟨hHsmooth, hHjets⟩ := hHm
  have hα := normalizedInverseParameter_smoothOn e L hL hd h8 heSmooth
  refine ⟨Phi, hunit, ?_⟩
  intro m
  refine pullbackDerivBound_of_gram_model g.form Phi (d / 16) (by positivity)
    (normalChartGram g p U e L d) hHsmooth ?_ Hbound hHbound ?_ m
  · intro z hz a b
    exact normalChartMap_pullback_eq_gram_entry g p U hU e L d z a b
      ((hα.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp))
      ((hunit.1.1.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp))
  · intro j z hz
    apply hHjets j z
    simpa only [div_div, show (16 : ℝ) * 2 = 32 by norm_num] using hz

theorem quantitativeHolomorphicCharts_all_dimensions (n : ℕ) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ℝ) (hK : ∀ m, 0 < K m) :
    ∃ rc c C : ℝ, 0 < rc ∧ 0 < c ∧ 0 < C ∧
      ∃ Cm : ℕ → ℝ, (∀ m, 0 < Cm m) ∧
        ∀ (M : ComplexManifold n) (k : HermitianField M) (p : M.Carrier),
          MetricSmooth k → KahlerClosed k → IsCompleteDistance (lengthDist k) →
          (∀ m x, x ∈ distBall k p (2 * r) → curvatureJetNorm k m x ≤ K m) →
          ∃ Phi : ComplexVector n → M.Carrier,
            UnitaryChart k p Phi rc c C ∧
              ∀ m, PullbackDerivBound k Phi (rc / 2) m (Cm m) := by
  by_cases hn : 0 < n
  · exact quantitativeHolomorphicCharts n hn r hr K hK
  · refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num,
      fun _ => 1, fun _ => by norm_num, ?_⟩
    intro M
    exact False.elim (hn (manifold_dimension_pos M))

end Yau.Proofs.C04ChartsAux
