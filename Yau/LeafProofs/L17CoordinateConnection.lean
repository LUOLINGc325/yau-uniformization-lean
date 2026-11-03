import Yau.LeafProofs.L17BackgroundMetric
import Yau.LeafProofs.L17MetricPullbackDerivative

/-! The real coordinate connection computed from the actual chart metric. -/

noncomputable section

open scoped Matrix ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ}

local instance connection_dualGroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance connection_dualSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance connection_bilinearGroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance connection_bilinearSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def bilinearMatrix (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    Matrix (RIdx n) (RIdx n) ℝ := fun a b => B (realVec a) (realVec b)

def inverseBilinear (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    (ComplexVector n →L[ℝ] ℝ) →L[ℝ] ComplexVector n :=
  ∑ c, ∑ b, (bilinearMatrix B)⁻¹ c b •
    (ContinuousLinearMap.apply ℝ ℝ (realVec b)).smulRight (realVec c)

theorem inverseBilinear_apply (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (f : ComplexVector n →L[ℝ] ℝ) :
    inverseBilinear B f =
      ∑ c, (∑ b, (bilinearMatrix B)⁻¹ c b * f (realVec b)) • realVec c := by
  simp only [inverseBilinear, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.apply_apply, smul_smul, Finset.sum_smul]

theorem bilinear_inverseBilinear
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (hsymm : ∀ u v, B u v = B v u) (hdet : IsUnit (bilinearMatrix B).det)
    (f : ComplexVector n →L[ℝ] ℝ) (w : ComplexVector n) :
    B (inverseBilinear B f) w = f w := by
  have hb (d : RIdx n) : B (inverseBilinear B f) (realVec d) = f (realVec d) := by
    let G := bilinearMatrix B
    let v : RIdx n → ℝ := fun b => f (realVec b)
    have hv : G *ᵥ (G⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    calc
      _ = (G *ᵥ (G⁻¹ *ᵥ v)) d := by
        rw [inverseBilinear_apply, map_sum, sum_apply]
        simp only [map_smul, smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro c _
        rw [hsymm]
        change (∑ b, G⁻¹ c b * v b) * G d c = G d c * (∑ b, G⁻¹ c b * v b)
        ring
      _ = _ := congrFun hv d
  have hlinear : (B (inverseBilinear B f)).toLinearMap = f.toLinearMap := by
    apply (L12Aux.realVec_basis n).ext
    intro d
    convert! hb d using 1 <;> rw [L12Aux.realVec_basis_apply] <;> rfl
  exact congrArg (fun L : ComplexVector n →ₗ[ℝ] ℝ => L w) hlinear

def koszulMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ((D + D.flip : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      D.flip)

theorem koszulMap_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    koszulMap D u v w = (D u v w + D v u w - D w u v) / 2 := by
  simp only [koszulMap, smul_apply, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearMap.coe_flipₗᵢ,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

def connectionBilinear (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (D : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n →L[ℝ] ℝ)
    (ComplexVector n) (inverseBilinear B)).comp (koszulMap D)

theorem connectionBilinear_apply
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (D : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (u v : ComplexVector n) :
    connectionBilinear B D u v = inverseBilinear B (koszulMap D u v) := rfl

theorem connectionBilinear_koszul
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (D : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (hsymm : ∀ u v, B u v = B v u) (hdet : IsUnit (bilinearMatrix B).det)
    (u v w : ComplexVector n) :
    B (connectionBilinear B D u v) w = (D u v w + D v u w - D w u v) / 2 := by
  rw [connectionBilinear_apply, bilinear_inverseBilinear B hsymm hdet, koszulMap_apply]

end Yau.LeafProofs.L17Aux
