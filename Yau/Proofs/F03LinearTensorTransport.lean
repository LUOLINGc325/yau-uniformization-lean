import Yau.Proofs.F03DirectionalTensor

/-! Literal derivative tensors under a genuine continuous linear equivalence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem iteratedFDeriv_comp_linearEquiv (P : E ≃L[ℝ] F) (f : F → ℝ) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (f ∘ P) x=
      (iteratedFDeriv ℝ m f (P x)).compContinuousLinearMap (fun _ => P.toContinuousLinearMap) := by
  have h := P.iteratedFDerivWithin_comp_right f (s := univ) (x := x) uniqueDiffOn_univ (mem_univ (P x)) m
  simpa only [preimage_univ,iteratedFDerivWithin_univ] using h

theorem norm_iteratedFDeriv_comp_linearEquiv_le (P : E ≃L[ℝ] F) (f : F → ℝ) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (f ∘ P) x‖ ≤
      (max 1 ‖P.toContinuousLinearMap‖)^m*‖iteratedFDeriv ℝ m f (P x)‖ := by
  rw [iteratedFDeriv_comp_linearEquiv]
  have hbase := (iteratedFDeriv ℝ m f (P x)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => P.toContinuousLinearMap)
  have hp : ‖P.toContinuousLinearMap‖^m ≤ (max 1 ‖P.toContinuousLinearMap‖)^m :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) m
  have hb : ‖(iteratedFDeriv ℝ m f (P x)).compContinuousLinearMap
      (fun _ : Fin m => P.toContinuousLinearMap)‖ ≤
      ‖iteratedFDeriv ℝ m f (P x)‖*‖P.toContinuousLinearMap‖^m := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hbase
  exact hb.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem norm_iteratedFDeriv_comp_linearEquiv_lt (P : E ≃L[ℝ] F) (f : F → ℝ)
    (m : ℕ) (x : E) (η : ℝ) (hη : 0 < η)
    (hsmall : ‖iteratedFDeriv ℝ m f (P x)‖ < η/(max 1 ‖P.toContinuousLinearMap‖)^m) :
    ‖iteratedFDeriv ℝ m (f ∘ P) x‖ < η := by
  have hR : 0 < (max 1 ‖P.toContinuousLinearMap‖)^m :=
    pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) m
  calc
    _ ≤ (max 1 ‖P.toContinuousLinearMap‖)^m*‖iteratedFDeriv ℝ m f (P x)‖ :=
      norm_iteratedFDeriv_comp_linearEquiv_le P f m x
    _ < (max 1 ‖P.toContinuousLinearMap‖)^m*(η/(max 1 ‖P.toContinuousLinearMap‖)^m) :=
      mul_lt_mul_of_pos_left hsmall hR
    _ = η := by field_simp

end Yau.Proofs.F03Aux
