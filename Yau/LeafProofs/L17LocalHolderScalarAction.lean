import Yau.LeafProofs.L17LocalHolderBanachAlgebra

noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17SchauderAux L17LocalHolderAlgebraAux L17LocalHolderBanachAlgebraAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {P : UniformChartPartition g} {T γ : ℝ}

def localScalarActionElement (u : LocalHolderBanach ℝ P T γ) (v : LocalHolderBanach F P T γ) :
    LocalHolderBanach F P T γ :=
  ⟨localBilinearCLM (ContinuousLinearMap.lsmul ℝ ℝ (E:=F)) u.value v.value⟩

theorem localScalarActionElement_value (u : LocalHolderBanach ℝ P T γ)
    (v : LocalHolderBanach F P T γ) (q : LocalCylinder P T) :
    localScalarActionElement u v q=u q • v q := rfl

theorem localScalarActionElement_norm_le (u : LocalHolderBanach ℝ P T γ)
    (v : LocalHolderBanach F P T γ) : ‖localScalarActionElement u v‖≤‖u‖*‖v‖ := by
  have hb := localBilinearElement_norm_le (ContinuousLinearMap.lsmul ℝ ℝ (E:=F)) u.value v.value
  have hb' : ‖localBilinearCLM (ContinuousLinearMap.lsmul ℝ ℝ (E:=F)) u.value v.value‖≤2*‖u.value‖*‖v.value‖ :=
    hb.trans (by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_lsmul_le (𝕜:=ℝ) (R:=ℝ) (E:=F)) (by norm_num : (0:ℝ)≤2))
  rw [norm_eq_twice,norm_eq_twice,norm_eq_twice]
  exact (mul_le_mul_of_nonneg_left hb' (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

def localScalarActionLinearMap (u : LocalHolderBanach ℝ P T γ) :
    LocalHolderBanach F P T γ →ₗ[ℝ] LocalHolderBanach F P T γ where
  toFun := localScalarActionElement u
  map_add' v w := by
    apply L17LocalHolderBanachAlgebraAux.ext
    intro q
    exact smul_add (u q) (v q) (w q)
  map_smul' c v := by
    apply L17LocalHolderBanachAlgebraAux.ext
    intro q
    exact smul_comm (u q) c (v q)

def localScalarActionCLM (u : LocalHolderBanach ℝ P T γ) :
    LocalHolderBanach F P T γ →L[ℝ] LocalHolderBanach F P T γ :=
  (localScalarActionLinearMap (F:=F) u).mkContinuous ‖u‖
    (fun v => localScalarActionElement_norm_le u v)

theorem localScalarActionCLM_value (u : LocalHolderBanach ℝ P T γ)
    (v : LocalHolderBanach F P T γ) (q : LocalCylinder P T) :
    localScalarActionCLM u v q=u q • v q := rfl

theorem localScalarActionCLM_opNorm_le (u : LocalHolderBanach ℝ P T γ) :
    ‖localScalarActionCLM (F:=F) u‖≤‖u‖ :=
  (localScalarActionCLM (F:=F) u).opNorm_le_bound (norm_nonneg _) (fun v => localScalarActionElement_norm_le u v)

end Yau.LeafProofs.L17Aux
