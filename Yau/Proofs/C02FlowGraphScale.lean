import Yau.Proofs.C02FlowCurvatureJets
import Yau.Proofs.C02NormalComplexUniformBounds
import Yau.Proofs.C02UniformIntegrableGraph

/-! Retaining the actual curvature profile identifies the one graph scale
with the same radius on which all metric and complex-structure bounds hold. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {X : KahlerManifold n}
local instance fgs_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance fgs_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem exists_uniform_flow_graph_scale
    (hL23 : Yau.LeafObligations.L23)
    (o : Pt X) (h : Flow X) (U₀ P ρ₀ : STF X)
    (hloc : LocalizedFlow X o h U₀ P ρ₀) (hC01 : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ r : ℝ,
      0 < r ∧ r ≤ 1 ∧ 2 * r < radialGaugeRadius (C 0) ∧
      ∀ t : ℝ, ∀ ht : 2 ≤ t, ∀ p ∈ K,
      (∀ j (y : Pt X), distFrom (h t) p y ≤ 1 → curvatureJetNorm (h t) j y ≤ C j) ∧
      ∀ (U : ComplexVector n ≃ₗ[ℂ] TangentVector X.manifold p)
        (hU : ∀ u v, (h t p).toFun (U u) (U v) = ⟪u, v⟫_ℂ),
      let g := completeFlowSlice X o h hloc.1 hC01 t (by linarith)
      let A := cayleyCoefficientMatrix (fun y => normalGaugeComplex g p U hU (r • y))
      L21Aux.MatrixSmoothOn A (Metric.ball 0 2) ∧
        L21Aux.CommutesOn A (Metric.ball 0 2) ∧
        L21Aux.JetBound q ε A (Metric.closedBall 0 2) ∧ A 0 = 0 := by
  obtain ⟨C, hC, hCurv⟩ := exists_uniform_flow_curvature_jet_bounds
    hL23 o h U₀ P ρ₀ hloc hC01 K hK
  let ρ := radialGaugeRadius (C 0)
  let d := fun i => (radialJetMajorant C ρ i).differential
  let b := binomialJetProduct (inverseJetMajorant d) d
  obtain ⟨r, hr, hr1, hrρ, hGraph⟩ := exists_uniform_integrable_graph_dilation n ρ
    (radialGaugeRadius_pos (hC 0).le) b q ε hε
  refine ⟨C, hC, r, hr, hr1, hrρ, ?_⟩
  intro t ht p hp
  have hRm (j : ℕ) (y : Pt X) (hy : distFrom (h t) p y ≤ 1) := hCurv t ht p hp j y hy
  refine ⟨hRm, ?_⟩
  intro U hU
  let g := completeFlowSlice X o h hloc.1 hC01 t (by linarith)
  let J := normalGaugeComplex g p U hU
  have hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 ρ) :=
    (normalGaugeComplex_smoothOn g p U hU (hC 0).le (hRm 0)).mono Metric.ball_subset_closedBall
  have hNorm (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) ρ) :
      ‖x‖ < radialGaugeRadius (C 0) := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  exact hGraph J hJ (normalGaugeComplex_zero g p U hU)
    (fun x hx v => normalGaugeComplex_square g p U hU (hC 0).le (hRm 0) x v (hNorm x hx).le)
    (fun x hx v w => normalGaugeComplex_nijenhuis_zero g p U hU (hC 0).le (hRm 0) x (hNorm x hx) v w)
    (fun x hx => (normalGaugeComplex_sub_standard_norm_le g p U hU (hC 0).le (hRm 0) x
      (hNorm x hx).le).trans (by norm_num))
    (fun m x hx => normalGaugeComplex_jet_norm_le g p U hU C (fun j => (hC j).le) hRm m x (hNorm x hx).le)

end Yau.Blueprint.C02Proof
