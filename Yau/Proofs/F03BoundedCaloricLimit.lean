import Yau.Proofs.F03BoundedCaloricValueLimit
import Yau.Proofs.F03CaloricPointwiseLimit
import Yau.Proofs.F03CaloricL2Tensor

/-! Genuine bounded classical limits: smoothness, the PDE, and literal all-order mixed convergence. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

theorem bounded_classical_caloric_limit
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O)
    (hOc : IsCompact (closure O))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (u : ℕ → Point d → ℝ) (v : Point d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (O ×ˢ Ioo l r))
    (hClass : ∀ j p,p ∈ O ×ˢ Ioo l r → linearOp (O ×ˢ Ioo l r) a b (u j) p=0)
    (hBound : ∀ j p,p ∈ O ×ˢ Ioo l r → |u j p| ≤ B)
    (hPoint : ∀ p ∈ O ×ˢ Ioo l r,Tendsto (fun j => u j p) atTop (𝓝 (v p))) :
    ContDiffOn ℝ ∞ v (O ×ˢ Ioo l r) ∧
      (∀ p ∈ O ×ˢ Ioo l r,linearOp (O ×ˢ Ioo l r) a b v p=0) ∧
      (∀ K : Set (Point d),IsCompact K → K ⊆ O ×ˢ Ioo l r →
        ∀ m : ℕ,∃ C : ℝ,0 < C ∧ ∀ j p,p ∈ K → ‖iteratedFDeriv ℝ m (u j) p‖ ≤ C) ∧
      (∀ K : Set (Point d),IsCompact K → K ⊆ O ×ˢ Ioo l r →
        ∀ (m : ℕ) (η : ℝ),0 < η → ∃ J : ℕ,∀ j,J ≤ j → ∀ p ∈ K,
          ‖iteratedFDeriv ℝ m (fun q => u j q-v q) p‖ < η) := by
  obtain ⟨hf,hvLp,hL2⟩ := bounded_cylinder_value_toLp_limit O l r hO hOc u v
    (fun j => (hu j).continuousOn) B hB hBound hPoint
  obtain ⟨hv,hvClass⟩ := classicalCaloric_pointwise_limit_smooth_of_value_cauchy hd O l r lam upper hO
    a b hAB hEll u v hu hClass hf hL2.cauchySeq hPoint
  refine ⟨hv,hvClass,?_,?_⟩
  · intro K hK hKD m
    obtain ⟨C,hC,hTensor⟩ := classicalCaloric_compact_tensor_L2_bound hd O l r lam upper hO
      a b hAB hEll K hK hKD m
    obtain ⟨R,hR,hRange⟩ := hL2.cauchySeq.isBounded_range.exists_pos_norm_le
    refine ⟨C*R,mul_pos hC hR,?_⟩
    intro j p hp
    have hNorm : (eLpNorm (u j) 2 (volume.restrict (O ×ˢ Ioo l r))).toReal ≤ R := by
      rw [← Lp.norm_toLp (u j) (hf j)]
      exact hRange _ ⟨j,rfl⟩
    exact (hTensor (u j) (hu j) (hClass j) (hf j) p hp).trans
      (mul_le_mul_of_nonneg_left hNorm hC.le)
  · intro K hK hKD m η hη
    obtain ⟨C,hC,hTensor⟩ := classicalCaloric_compact_tensor_L2_bound hd O l r lam upper hO
      a b hAB hEll K hK hKD m
    have hn : Tendsto (fun j => ‖(hf j).toLp (u j)-hvLp.toLp v‖) atTop (𝓝 (0 : ℝ)) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hL2
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds (div_pos hη hC)))
    refine ⟨J,fun j hj p hp => ?_⟩
    have hDiff : ∀ q ∈ O ×ˢ Ioo l r,linearOp (O ×ˢ Ioo l r) a b (fun s => u j s-v s) q=0 := by
      intro q hq
      rw [local_linearOp_sub (hO.prod isOpen_Ioo) a b (hu j) hv hq,hClass j q hq,hvClass q hq,sub_self]
    have hNorm : (eLpNorm (fun q => u j q-v q) 2 (volume.restrict (O ×ˢ Ioo l r))).toReal=
        ‖(hf j).toLp (u j)-hvLp.toLp v‖ := by
      rw [← MemLp.toLp_sub (hf j) hvLp,Lp.norm_toLp]
      rfl
    calc
      _ ≤ C*(eLpNorm (fun q => u j q-v q) 2 (volume.restrict (O ×ˢ Ioo l r))).toReal :=
        hTensor (fun q => u j q-v q) ((hu j).sub hv) hDiff ((hf j).sub hvLp) p hp
      _ = C*‖(hf j).toLp (u j)-hvLp.toLp v‖ := by rw [hNorm]
      _ < C*(η/C) := mul_lt_mul_of_pos_left (hJ j hj) hC
      _ = η := by field_simp

end Yau.Proofs.F03Aux
