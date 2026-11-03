import Yau.Proofs.F01ProductTensorHolder

/-! A contraction on the tensor target preserves the Holder bound for
the actual spatial jet. In particular this applies to evaluation of a
covector in any unit native direction. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F G : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem holderBound_spatial_tensor_linear_contraction
    {Q : Set (Point n)} {S : Set (Space n)} {β C : ℝ} {f : Point n → F}
    (k : ℕ) (hS : IsOpen S) (hQ : Q ⊆ S ×ˢ (Set.univ : Set ℝ))
    (hfs : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S)
    (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (hf : HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) C) :
    HolderBound β Q (fun p => iteratedFDeriv ℝ k
      (fun z => L (f (z, p.2))) p.1) C := by
  have he (p : Point n) (hp : p ∈ Q) :
      iteratedFDeriv ℝ k (fun z => L (f (z, p.2))) p.1 =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) :=
    L.iteratedFDeriv_comp_left ((hfs p hp).contDiffAt (hS.mem_nhds (hQ hp).1)) (by simp)
  have hNorm (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F) :
      ‖L.compContinuousMultilinearMap A‖ ≤ ‖A‖ :=
    (L.norm_compContinuousMultilinearMap_le A).trans
      ((mul_le_mul_of_nonneg_right hL (norm_nonneg A)).trans_eq (one_mul _))
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    dsimp only
    rw [he p hp]
    exact (hNorm _).trans (hf.2.1 p hp)
  · intro p hp q hq
    dsimp only
    rw [he p hp, he q hq]
    have hsub : L.compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) -
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fun z => f (z, q.2)) q.1) =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1 -
          iteratedFDeriv ℝ k (fun z => f (z, q.2)) q.1) := by
      ext m
      exact (map_sub L _ _).symm
    rw [hsub]
    exact (hNorm _).trans (hf.2.2 p hp q hq)

theorem covector_evaluation_norm_le_one (v : Space n) (hv : ‖v‖ ≤ 1) :
    ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ 1 := by
  let L : (Space n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  change ‖L‖ ≤ 1
  apply L.opNorm_le_bound zero_le_one
  intro A
  change ‖A v‖ ≤ 1 * ‖A‖
  exact (A.le_opNorm v).trans
    ((mul_le_of_le_one_right (norm_nonneg A) hv).trans_eq (one_mul _).symm)

end Yau.NodeProofs.F01Aux
