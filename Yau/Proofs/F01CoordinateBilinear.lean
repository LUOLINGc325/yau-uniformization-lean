import spec.CHAIN.CONTRACTS

/-! Actual continuous complex bilinear maps from finite coordinate arrays,
used to prescribe the quadratic holomorphic coordinate jet. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

def coordinateBilinear (B : Fin n → Fin n → Fin n → ℂ) :
    ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n :=
  ∑ i, ∑ j, ∑ k, B i j k •
    (EuclideanSpace.proj j : ComplexVector n →L[ℂ] ℂ).smulRight
      ((EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).smulRight (stdVec i))

theorem coordinateBilinear_apply (B : Fin n → Fin n → Fin n → ℂ)
    (v w : ComplexVector n) :
    coordinateBilinear B v w =
      ∑ i, ∑ j, ∑ k, (B i j k * v j * w k) • stdVec i := by
  simp only [coordinateBilinear, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj, PiLp.proj_apply, smul_smul]

theorem coordinateBilinear_coordinate (B : Fin n → Fin n → Fin n → ℂ)
    (v w : ComplexVector n) (i : Fin n) :
    coordinateBilinear B v w i = ∑ j, ∑ k, B i j k * v j * w k := by
  rw [coordinateBilinear_apply]
  simp [stdVec, EuclideanSpace.single, Pi.single_apply, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, mul_ite]

theorem coordinateBilinear_symmetric (B : Fin n → Fin n → Fin n → ℂ)
    (hB : ∀ i j k, B i j k = B i k j) (v w : ComplexVector n) :
    coordinateBilinear B v w = coordinateBilinear B w v := by
  ext i
  rw [coordinateBilinear_coordinate, coordinateBilinear_coordinate, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [hB i j k]
  ring

end Yau.NodeProofs.F01Aux
