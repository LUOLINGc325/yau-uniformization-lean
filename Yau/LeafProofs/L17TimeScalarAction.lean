import Yau.LeafProofs.L17TimeFactorHolder
import Yau.LeafProofs.L17LocalHolderScalarAction

noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17SchauderAux L17LocalHolderBanachAlgebraAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (P : UniformChartPartition g) {T γ : ℝ}

def timeScalarActionCLM (hT : 0<T) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1) :
    LocalHolderBanach F P T γ →L[ℝ] LocalHolderBanach F P T γ :=
  localScalarActionCLM (timeFactorBanach P hT hγ hγ2 hr)

theorem timeScalarActionCLM_value (hT : 0<T) (hγ : 0≤γ) (hγ2 : γ≤2) (hr : P.radius≤1)
    (u : LocalHolderBanach F P T γ) (q : LocalCylinder P T) :
    timeScalarActionCLM P hT hγ hγ2 hr u q=(q.2.2 : ℝ) • u q := rfl

theorem timeScalarActionCLM_norm_le (hT : 0<T) (hTone : T≤1) (hγ : 0≤γ)
    (hγ2 : γ≤2) (hr : P.radius≤1) (u : LocalHolderBanach F P T γ) :
    ‖timeScalarActionCLM P hT hγ hγ2 hr u‖≤(2*T^(1-γ/2))*‖u‖ :=
  (localScalarActionElement_norm_le _ u).trans
    (mul_le_mul_of_nonneg_right (timeFactorBanach_norm_le P hT hTone hγ hγ2 hr) (norm_nonneg _))

theorem timeScalarActionCLM_opNorm_le (hT : 0<T) (hTone : T≤1) (hγ : 0≤γ)
    (hγ2 : γ≤2) (hr : P.radius≤1) :
    ‖timeScalarActionCLM (F:=F) P hT hγ hγ2 hr‖≤2*T^(1-γ/2) :=
  (localScalarActionCLM_opNorm_le _).trans (timeFactorBanach_norm_le P hT hTone hγ hγ2 hr)

end Yau.LeafProofs.L17Aux
