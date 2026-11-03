import Yau.Proofs.F05HolderInterpolation
import Yau.LeafProofs.L16CompatibleHolderGraph

/-! Common original Hölder control plus actual uniform value Cauchy data
produce a genuine native complete Hölder graph limit at half the exponent. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_holder_graph_half_cauchy {α C : ℝ} {Q : Set (Point n)}
    (u : ℕ → holderGraph (α/2) Q)
    (hBound : ∀ k, HolderBound α Q (holderGraphFun (u k)) C)
    (hCauchy : UniformCauchySeqOn (fun k => holderGraphFun (u k)) atTop Q) :
    CauchySeq u := by
  letI : NormedAddCommGroup (holderGraph (α/2) Q) := inferInstance
  letI : NormedSpace ℝ (holderGraph (α/2) Q) := inferInstance
  have hC : 0 ≤ C := (hBound 0).1
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := min (ε/4) (ε^2/(64*(C+1)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ ≤ ε/4 := min_le_left _ _
  have hδ2 : δ*(64*(C+1)) ≤ ε^2 :=
    (le_div_iff₀ (by positivity : 0 < 64*(C+1))).mp (min_le_right _ _)
  have hRad : 4*δ*C ≤ (ε/4)^2 := by nlinarith
  have hRoot : Real.sqrt (4*δ*C) ≤ ε/4 := (Real.sqrt_le_iff).mpr ⟨by positivity,hRad⟩
  obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hCauchy δ hδ
  refine ⟨N,?_⟩
  intro m hm k hk
  have hSup : ∀ p ∈ Q, ‖holderGraphFun (u m) p-holderGraphFun (u k) p‖ ≤ δ := by
    intro p hp
    exact (show ‖holderGraphFun (u m) p-holderGraphFun (u k) p‖ < δ by
      simpa only [dist_eq_norm] using hN m hm k hk p hp).le
  have hDiff := F05_holder_half_interpolation hδ.le (holderBound_sub (hBound m) (hBound k)) hSup
  have hActual : HolderBound (α/2) Q (holderGraphFun (u m-u k))
      (δ+Real.sqrt (4*δ*C)) := by
    have hBudget : 2*δ*(C+C) = 4*δ*C := by ring
    rw [hBudget] at hDiff
    apply holderBound_congr_on hDiff
    intro p hp
    change holderGraphFun (u m) p-holderGraphFun (u k) p = holderGraphFun (u m-u k) p
    rw [holderGraphFun_apply (u m) ⟨p,hp⟩,holderGraphFun_apply (u k) ⟨p,hp⟩,
      holderGraphFun_apply (u m-u k) ⟨p,hp⟩]
    rfl
  have hNorm := holderGraph_norm_le_of_holderBound (u m-u k) hActual
  have hDist : dist (u m) (u k) = ‖u m-u k‖ := by
    change max (dist (u m).val.1 (u k).val.1) (dist (u m).val.2 (u k).val.2) =
      max ‖(u m).val.1-(u k).val.1‖ ‖(u m).val.2-(u k).val.2‖
    rw [dist_eq_norm,dist_eq_norm]
  rw [hDist]
  exact hNorm.trans_lt (by linarith)

theorem F05_holder_graph_half_limit {α C : ℝ} {Q : Set (Point n)}
    (u : ℕ → holderGraph (α/2) Q)
    (hBound : ∀ k, HolderBound α Q (holderGraphFun (u k)) C)
    (hCauchy : UniformCauchySeqOn (fun k => holderGraphFun (u k)) atTop Q) :
    ∃ uLim : holderGraph (α/2) Q, Tendsto u atTop (𝓝 uLim) ∧
      ∀ p : Point n, Tendsto (fun k => holderGraphFun (u k) p) atTop (𝓝 (holderGraphFun uLim p)) := by
  obtain ⟨uLim,hu⟩ := cauchySeq_tendsto_of_complete (F05_holder_graph_half_cauchy u hBound hCauchy)
  exact ⟨uLim,hu,fun p => ((compatibleHolderGraph_eval_continuous p).tendsto uLim).comp hu⟩

end Yau.Proofs.F05Aux
