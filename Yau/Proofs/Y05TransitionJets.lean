import Yau.Proofs.Y05Clock
import Yau.Proofs.Y05CompositionEstimates
import Yau.Proofs.U02TransitionContinuation

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint Filter
open scoped Topology ContDiff BigOperators

variable {n : ℕ}

theorem shrinking_uniform_transition_jets {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {ρ : STF X} {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f) (d : ℕ) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ t t', t₀ ≤ t → t ≤ t' → jetNorm (F t t') d ≤ U := by
  rcases hc with ⟨hr, hr0, hσ, hC, hcharts, htrans, hcomp, hf0, hinv, hdec, hj, hreg⟩
  have hCb : 0 ≤ Cb := (norm_nonneg (F t₀ t₀ 0)).trans
    (((htrans t₀ t₀ le_rfl le_rfl).2.1 0 (Metric.mem_ball_self hr)).2)
  let S := ∑ m ∈ Finset.range (d + 1), (2 * ((m : ℝ) + 1) / r₁) ^ m
  have hS : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  refine ⟨1 + Cb * S, by nlinarith, ?_⟩
  intro t t' ht htt
  have hT := htrans t t' ht htt
  have hSmooth := Yau.Blueprint.V03Proof.complex_holomorphic_contDiffOn Metric.isOpen_ball hT.1
  have hb (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) r₁) :
      ‖F t t' z‖ ≤ Cb := (hT.2.1 z hz).2
  have H : jetNorm (F t t') d ≤ Cb * S := by
    unfold jetNorm S
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun m hm =>
      U02AnalyticAux.norm_iteratedFDeriv_center_le hr hCb hSmooth hb m
  linarith

theorem finiteJetNorm_congr {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f g : ComplexVector n → G} (h : f =ᶠ[𝓝 0] g) (d : ℕ) :
    finiteJetNorm f d = finiteJetNorm g d := by
  unfold finiteJetNorm
  apply Finset.sum_congr rfl
  intro m hm
  rw [(h.iteratedFDeriv ℂ m).eq_of_nhds]

theorem norm_jet_component_le (F : ComplexVector n → ComplexVector n) {m d : ℕ}
    (hm : m ≤ d) : ‖iteratedFDeriv ℂ m F 0‖ ≤ jetNorm F d := by
  unfold jetNorm
  exact Finset.single_le_sum (s := Finset.range (d + 1))
    (f := fun j => ‖iteratedFDeriv ℂ j F 0‖) (fun j _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega))

end Yau.Proofs.Y05Aux
