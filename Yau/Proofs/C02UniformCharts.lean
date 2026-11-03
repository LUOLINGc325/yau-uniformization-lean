import Yau.Proofs.C02FlowGraphFamily
import Yau.Proofs.C02CorrectedNormalChartJets
import Yau.Proofs.C02NativeCoordinateRegularity
import Yau.Proofs.C02GraphCoordinateIntertwining
import Yau.LeafProofs.L21WeightedDomains
import Yau.LeafProofs.L21SmallColumnCoordinates

/-! Every chart constant precedes all late times and centres.
The correcting function is obtained from the actual native weighted complex. -/

noncomputable section
open Set MeasureTheory
open scoped Manifold InnerProductSpace ContDiff Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {X : KahlerManifold n}
local instance uc_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance uc_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem uniformCharts_of_harnackCompleteness
    (hL23 : Yau.LeafObligations.L23)
    (o : Pt X) (h : Flow X) (U₀ P ρ₀ : STF X)
    (hloc : LocalizedFlow X o h U₀ P ρ₀) (hC01 : HarnackCompleteness X o h) :
    UniformCharts X h := by
  intro K hK
  obtain ⟨εW, W, hεW, hW, hSolve⟩ := L21Aux.weightedDomains_exists_small_column_solutions n
  obtain ⟨δ, hδ, hCoordinates⟩ := L21Aux.exists_small_weighted_column_coordinates (n := n) W hW.le
  let τ : ℝ := 1 / (2 * ((n : ℝ) ^ 2 + 1))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  let ε := min εW (min δ (min 1 τ))
  have hε : 0 < ε := lt_min hεW (lt_min hδ (lt_min zero_lt_one hτ))
  have hεW' : ε ≤ εW := min_le_left _ _
  have hεδ : ε ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hετ : ε ≤ τ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let q := max 2 (L21Aux.realDimension n + 1)
  have hq2 : 2 ≤ q := le_max_left _ _
  have hqR : L21Aux.realDimension n + 1 ≤ q := le_max_right _ _
  obtain ⟨C, hC, r, hr, hr1, hrρ, a, ha, hGraphs⟩ :=
    exists_uniform_flow_graph_family hL23 o h U₀ P ρ₀ hloc hC01 K hK q ε hε
  obtain ⟨b, hb, hFRegular⟩ := exists_uniform_coordinate_jet_profile n a
  let ρ := radialGaugeRadius (C 0)
  let dB := fun i => (radialJetMajorant C ρ i).differential
  let hB := binomialJetProduct dB dB
  obtain ⟨d, hChart⟩ := exists_uniform_corrected_normal_charts (n := n) r hr hB b
  refine ⟨r / 128, 1 / 128, 64, 2, by positivity, by norm_num, by norm_num,
    fun m _ => d m, ?_⟩
  intro t ht p hp
  have hFamily := hGraphs t ht p hp
  obtain ⟨U, hU⟩ := exists_unitaryTangentFrame (h t) p
  let g := completeFlowSlice X o h hloc.1 hC01 t (by linarith)
  let J := fun y => normalGaugeComplex g p U hU (r • y)
  let A := cayleyCoefficientMatrix J
  obtain ⟨hBefore, hAllA⟩ := hFamily.2 U hU
  obtain ⟨hASmooth, hComm, hASmall, hA0⟩ := hBefore
  have hJet (j : ℕ) (hj : j ≤ q) (E : ℝ) (hεE : ε ≤ E)
      {O : Set (ComplexVector n)} (hO : O ⊆ Metric.closedBall (0 : ComplexVector n) 2) :
      L21Aux.JetBound j E A O := by
    intro i hi x hx k l
    exact (hASmall i (hi.trans hj) x (hO hx) k l).trans hεE
  have hHalf : Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ) ⊆ Metric.ball 0 2 :=
    Metric.ball_subset_ball (by norm_num)
  have hOne : Metric.ball (0 : ComplexVector n) 1 ⊆ Metric.ball 0 2 :=
    Metric.ball_subset_ball (by norm_num)
  have hOp (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) 2) :
      LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2 :=
    L21Aux.jetBound_small_matrixOpNorm
      (hJet q le_rfl τ hετ (hO := Metric.ball_subset_closedBall)) x hx
  have hSolutions : ∀ k : Fin n, ∃ u : ComplexVector n → ℂ,
      MemLp u 2 (L21Aux.weightedBallMeasure n W) ∧
      L21Aux.DbarWeakOn A u (fun x i => A x i k) (Metric.ball 0 1) ∧
      (∫ x, ‖u x‖ ^ 2 ∂L21Aux.weightedBallMeasure n W) ≤
        ∑ j, ∫ x, ‖(L21Aux.rho x : ℂ) * A x j k‖ ^ 2 ∂L21Aux.weightedBallMeasure n W := by
    intro k
    obtain ⟨u, hu, _hLocal, hWeak, hMass⟩ := hSolve A hASmooth
      (hJet 1 (by omega) εW hεW' Metric.ball_subset_closedBall)
      (hJet 2 hq2 1 hε1 Metric.ball_subset_closedBall) hComm k
    exact ⟨u, hu, hWeak, hMass⟩
  obtain ⟨F, hF, hEquation, hClose⟩ := hCoordinates A
    (fun i k => (hASmooth i k).mono hOne) (fun x hx => hOp x (hOne hx))
    (hJet _ hqR 1 hε1 (hOne.trans Metric.ball_subset_closedBall))
    (hJet _ hqR δ hεδ (hOne.trans Metric.ball_subset_closedBall)) hSolutions
  have hAValue (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ))
      (i k : Fin n) : ‖A x i k‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_zero] using
      hJet 0 (by omega) 1 hε1 (hHalf.trans Metric.ball_subset_closedBall) 0 le_rfl x hx i k
  have hFJets := hFRegular A (fun i k => (hASmooth i k).mono hHalf)
    (fun x hx => hOp x (hHalf hx)) hAValue
    (fun j hj x hx i k => hAllA j x (hHalf hx) i k) F hF hEquation hClose
  have hRm (j : ℕ) (y : Pt X) (hy : inducedDistance g.form p y ≤ 1) :
      curvatureJetNorm g.form j y ≤ C j := hFamily.1 j y hy
  have hMetric (i : ℕ) (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius (C 0)) :
      ‖iteratedFDeriv ℝ i (normalGaugeMetric g p U hU) x‖ ≤ hB i :=
    normalGaugeMetric_jet_norm_le g p U hU C (fun j => (hC j).le) hRm i x hx
  have hForward (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ))
      (v : ComplexVector n) :
      fderiv ℝ F x (normalGaugeComplex g p U hU (r • x) v) = Complex.I • fderiv ℝ F x v := by
    have hx2 : x ∈ Metric.ball (0 : ComplexVector n) 2 := Metric.ball_subset_ball (by norm_num) hx
    have hxNormal : ‖r • x‖ ≤ radialGaugeRadius (C 0) :=
      (by simpa only [Metric.mem_ball, dist_zero_right] using
        smul_closedBall_two_mem hr hrρ (Metric.ball_subset_closedBall hx2) :
        ‖r • x‖ < radialGaugeRadius (C 0)).le
    apply graph_coordinate_differential_intertwines J F x (hF.differentiable (by simp) x)
    · intro w
      exact normalGaugeComplex_square g p U hU (hC 0).le (hRm 0) (r • x) w hxNormal
    · exact (normalGaugeComplex_sub_standard_norm_le g p U hU (hC 0).le (hRm 0) _ hxNormal).trans (by norm_num)
    · exact hEquation x (Metric.ball_subset_ball (by norm_num) hx)
  exact hChart X.manifold g p U hU (C 0) (hC 0).le hrρ (hRm 0) hMetric F hF
    (fun x hx => hClose x (Metric.ball_subset_ball (by norm_num) hx)) hFJets hForward

end Yau.Blueprint.C02Proof
