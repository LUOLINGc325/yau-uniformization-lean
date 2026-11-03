import Yau.Proofs.F03DyadicLeviIdentity
import Yau.Proofs.F03DyadicLeviProfiles

/-! Exact derivative support and genuine two-sided matrix control of the dyadic product error. -/
noncomputable section
open scoped ComplexOrder Matrix ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

def dyadicLeviError (u f : M.Carrier → ℝ) (j : ℕ) (x : M.Carrier) : Herm n :=
  Complex.ofReal (f x) • levi (fun y => dyadicPartition j (u y)) x+
    (Matrix.vecMulVec (star (scalarFirstCovector (fun y => dyadicPartition j (u y)) x))
      (scalarFirstCovector f x)+
     Matrix.vecMulVec (star (scalarFirstCovector f x))
      (scalarFirstCovector (fun y => dyadicPartition j (u y)) x))

theorem dyadicLeviError_zero (u f : M.Carrier → ℝ) (hu : SmoothFn u) (j : ℕ) (x : M.Carrier)
    (hZero : deriv (dyadicPartition j) (u x)=0)
    (hZero' : deriv (deriv (dyadicPartition j)) (u x)=0) : dyadicLeviError u f j x=0 := by
  unfold dyadicLeviError
  rw [dyadicProfile_levi_zero u hu j x hZero hZero',dyadicProfile_covector_zero u hu j x hZero]
  simp [Matrix.vecMulVec_apply]

theorem dyadicLeviError_abs_bound (g : HermitianField M)
    (u f : M.Carrier → ℝ) (hu : SmoothFn u) (hf : SmoothFn f) (j : ℕ) (x : M.Carrier)
    {B Q θ : ℝ} (hB : 0 < B) (hQ : 0 < Q) (hu0 : 0 < u x)
    (hProfileGrad : Real.sqrt (gradNormSq g (fun y => dyadicPartition j (u y)) x) ≤ Q/u x)
    (hProfileLevi : HermAbsLE (levi (fun y => dyadicPartition j (u y)) x) (gMat g x) (Q/(u x)^2))
    (hSize : |f x| ≤ B*(u x)^(2-θ))
    (hGrad : Real.sqrt (gradNormSq g f x) ≤ B*(u x)^(1-θ)) :
    HermAbsLE (dyadicLeviError u f j x) (gMat g x) (3*B*Q/(u x)^θ) := by
  have hProfileSmooth : SmoothFn (fun y => dyadicPartition j (u y)) :=
    fun a => (dyadicPartition_contDiff j).comp_contDiffOn (hu a)
  have hCross := scalarFirstCovector_cross_abs_bound g hProfileSmooth hf x
    (div_pos hQ hu0) (mul_pos hB (Real.rpow_pos_of_pos hu0 _)) hProfileGrad hGrad
  have hProduct := hermAbsLE_real_smul hProfileLevi (f x)
  have hBoth := hermAbsLE_add hProduct hCross
  have hPower : 0 < (u x)^θ := Real.rpow_pos_of_pos hu0 _
  have hPow₂ : (u x)^(2-θ)/(u x)^2=1/(u x)^θ := by
    rw [Real.rpow_sub hu0 2 θ,Real.rpow_two]
    field_simp
  have hPow₁ : (u x)^(1-θ)/(u x)=1/(u x)^θ := by
    rw [Real.rpow_sub hu0 1 θ,Real.rpow_one]
    field_simp
  apply hermAbsLE_mono (hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef hBoth
  calc
    _ ≤ (B*(u x)^(2-θ))*(Q/(u x)^2)+2*(Q/u x)*(B*(u x)^(1-θ)) :=
      add_le_add (mul_le_mul_of_nonneg_right hSize (by positivity)) le_rfl
    _ = (B*Q)*((u x)^(2-θ)/(u x)^2)+(2*B*Q)*((u x)^(1-θ)/u x) := by ring
    _ = _ := by rw [hPow₂,hPow₁];ring

end Yau.Proofs.F03Aux
