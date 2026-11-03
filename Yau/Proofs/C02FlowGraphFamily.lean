import Yau.Proofs.C02FlowGraphScale
import Yau.Proofs.C02UniformScaledGraphJets

/-! The finite smallness scale and the all-order coefficient profile are
fixed together before all late times, compact centres and unitary frames. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {X : KahlerManifold n}
local instance fgf_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance fgf_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem exists_uniform_flow_graph_family
    (hL23 : Yau.LeafObligations.L23)
    (o : Pt X) (h : Flow X) (U₀ P ρ₀ : STF X)
    (hloc : LocalizedFlow X o h U₀ P ρ₀) (hC01 : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ r : ℝ,
      0 < r ∧ r ≤ 1 ∧ 2 * r < radialGaugeRadius (C 0) ∧
      ∃ a : ℕ → ℝ, (∀ j, 0 ≤ a j) ∧
      ∀ t : ℝ, ∀ ht : 2 ≤ t, ∀ p ∈ K,
      (∀ j (y : Pt X), distFrom (h t) p y ≤ 1 → curvatureJetNorm (h t) j y ≤ C j) ∧
      ∀ (U : ComplexVector n ≃ₗ[ℂ] TangentVector X.manifold p)
        (hU : ∀ u v, (h t p).toFun (U u) (U v) = ⟪u, v⟫_ℂ),
      let g := completeFlowSlice X o h hloc.1 hC01 t (by linarith)
      let A := cayleyCoefficientMatrix (fun y => normalGaugeComplex g p U hU (r • y))
      (L21Aux.MatrixSmoothOn A (Metric.ball 0 2) ∧
        L21Aux.CommutesOn A (Metric.ball 0 2) ∧
        L21Aux.JetBound q ε A (Metric.closedBall 0 2) ∧ A 0 = 0) ∧
      ∀ j x, x ∈ Metric.ball (0 : ComplexVector n) 2 → ∀ i k,
        ‖iteratedFDeriv ℝ j (fun y => A y i k) x‖ ≤ a j := by
  obtain ⟨C, hC, r, hr, hr1, hrρ, hGraphs⟩ :=
    exists_uniform_flow_graph_scale hL23 o h U₀ P ρ₀ hloc hC01 K hK q ε hε
  let ρ := radialGaugeRadius (C 0)
  let d := fun i => (radialJetMajorant C ρ i).differential
  let b := binomialJetProduct (inverseJetMajorant d) d
  obtain ⟨a, ha, hAll⟩ := exists_uniform_scaled_graph_jet_bounds n ρ b r hr hr1 hrρ
  refine ⟨C, hC, r, hr, hr1, hrρ, a, ha, ?_⟩
  intro t ht p hp
  have hBefore := hGraphs t ht p hp
  refine ⟨hBefore.1, ?_⟩
  intro U hU
  refine ⟨hBefore.2 U hU, ?_⟩
  let g := completeFlowSlice X o h hloc.1 hC01 t (by linarith)
  let J := normalGaugeComplex g p U hU
  have hRm (j : ℕ) (y : Pt X) (hy : distFrom (h t) p y ≤ 1) := hBefore.1 j y hy
  have hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 ρ) :=
    (normalGaugeComplex_smoothOn g p U hU (hC 0).le (hRm 0)).mono Metric.ball_subset_closedBall
  have hNorm (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) ρ) : ‖x‖ ≤ ρ :=
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < ρ).le
  exact hAll J hJ
    (fun x hx => (normalGaugeComplex_sub_standard_norm_le g p U hU (hC 0).le (hRm 0)
      x (hNorm x hx)).trans (by norm_num))
    (fun j x hx => normalGaugeComplex_jet_norm_le g p U hU C (fun i => (hC i).le) hRm j x (hNorm x hx))

end Yau.Blueprint.C02Proof
