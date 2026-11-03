import Yau.Proofs.F05HolderGraphLimit
import Yau.Proofs.F05VectorHolder

/-! The actual vector Hölder graph has the same quantitative compactness
mechanism, applied in particular to the true Hessian component. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_vector_holder_graph_norm_le {α C : ℝ} {Q : Set (Point n)}
    (u : vectorHolderGraph V α Q) (hu : HolderBound α Q (vectorHolderFun u) C) : ‖u‖ ≤ C := by
  change max ‖u.val.1‖ ‖u.val.2‖ ≤ C
  apply max_le
  · apply (BoundedContinuousFunction.norm_le hu.1).mpr
    intro p
    simpa only [vectorHolderFun_apply u p] using hu.2.1 p.val p.property
  · apply (BoundedContinuousFunction.norm_le hu.1).mpr
    intro z
    have hW := holderPair_weight_pos α z
    have h := hu.2.2 z.val.1.val z.val.1.property z.val.2.val z.val.2.property
    rw [vectorHolderFun_apply u z.val.1,vectorHolderFun_apply u z.val.2,u.property z,
      norm_smul,Real.norm_eq_abs,abs_of_pos hW] at h
    exact (mul_le_mul_iff_right₀ hW).mp (h.trans_eq (mul_comm C _))

theorem F05_vector_holder_graph_half_cauchy {α C : ℝ} {Q : Set (Point n)}
    (u : ℕ → vectorHolderGraph V (α/2) Q)
    (hBound : ∀ k, HolderBound α Q (vectorHolderFun (u k)) C)
    (hCauchy : UniformCauchySeqOn (fun k => vectorHolderFun (u k)) atTop Q) :
    CauchySeq u := by
  letI : NormedAddCommGroup (vectorHolderGraph V (α/2) Q) := inferInstance
  letI : NormedSpace ℝ (vectorHolderGraph V (α/2) Q) := inferInstance
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
  have hSup : ∀ p ∈ Q, ‖vectorHolderFun (u m) p-vectorHolderFun (u k) p‖ ≤ δ := by
    intro p hp
    exact (show ‖vectorHolderFun (u m) p-vectorHolderFun (u k) p‖ < δ by
      simpa only [dist_eq_norm] using hN m hm k hk p hp).le
  have hDiff := F05_holder_half_interpolation hδ.le (holderBound_sub (hBound m) (hBound k)) hSup
  have hActual : HolderBound (α/2) Q (vectorHolderFun (u m-u k))
      (δ+Real.sqrt (4*δ*C)) := by
    rw [show 2*δ*(C+C) = 4*δ*C by ring] at hDiff
    apply holderBound_congr_on hDiff
    intro p hp
    change vectorHolderFun (u m) p-vectorHolderFun (u k) p = vectorHolderFun (u m-u k) p
    rw [vectorHolderFun_apply (u m) ⟨p,hp⟩,vectorHolderFun_apply (u k) ⟨p,hp⟩,
      vectorHolderFun_apply (u m-u k) ⟨p,hp⟩]
    rfl
  have hNorm := F05_vector_holder_graph_norm_le (u m-u k) hActual
  have hDist : dist (u m) (u k) = ‖u m-u k‖ := by
    change max (dist (u m).val.1 (u k).val.1) (dist (u m).val.2 (u k).val.2) =
      max ‖(u m).val.1-(u k).val.1‖ ‖(u m).val.2-(u k).val.2‖
    rw [dist_eq_norm,dist_eq_norm]
  rw [hDist]
  exact hNorm.trans_lt (by linarith)

theorem F05_vector_holder_graph_half_limit [CompleteSpace V] {α C : ℝ} {Q : Set (Point n)}
    (u : ℕ → vectorHolderGraph V (α/2) Q)
    (hBound : ∀ k, HolderBound α Q (vectorHolderFun (u k)) C)
    (hCauchy : UniformCauchySeqOn (fun k => vectorHolderFun (u k)) atTop Q) :
    ∃ uLim : vectorHolderGraph V (α/2) Q, Tendsto u atTop (𝓝 uLim) ∧
      ∀ p : Point n, Tendsto (fun k => vectorHolderFun (u k) p) atTop (𝓝 (vectorHolderFun uLim p)) := by
  obtain ⟨uLim,hu⟩ := cauchySeq_tendsto_of_complete (F05_vector_holder_graph_half_cauchy u hBound hCauchy)
  exact ⟨uLim,hu,fun p => ((vectorHolderFun_eval_continuous p).tendsto uLim).comp hu⟩

end Yau.Proofs.F05Aux
