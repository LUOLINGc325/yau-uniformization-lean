import Yau.Proofs.E02RectangularLevi
import Yau.Proofs.E02WeightedColumns

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- One genuine column direction in the fixed rectangular coordinates. -/
def singleColumn {n m : ℕ} (j : Fin m) (V : ComplexVector n) : Rect n m :=
  Matrix.vecMulVec (WithLp.ofLp V) (Pi.single j 1)

theorem trace_singleColumn {n m : ℕ} (B : Herm n) (Q : Herm m)
    (j : Fin m) (V : ComplexVector n) :
    Matrix.trace (B*singleColumn j V*Q*(singleColumn j V)ᴴ) =
      Q j j*(star (WithLp.ofLp V) ⬝ᵥ (B*ᵥWithLp.ofLp V)) := by
  have he : star (Pi.single j (1 : ℂ) : Fin m → ℂ) = Pi.single j 1 := by
    ext k
    by_cases h : k=j <;> simp [h]
  have hLeft : B*singleColumn j V*Q =
      Matrix.vecMulVec (B*ᵥWithLp.ofLp V) ((Pi.single j 1) ᵥ*Q) := by
    rw [singleColumn,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul]
  have hAdj : (singleColumn j V)ᴴ = Matrix.vecMulVec (Pi.single j 1) (star (WithLp.ofLp V)) := by
    rw [singleColumn,Matrix.conjTranspose_vecMulVec,he]
  rw [hLeft,hAdj,Matrix.vecMulVec_mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_smul]
  have hdiag : ((Pi.single j (1 : ℂ)) ᵥ*Q) ⬝ᵥ Pi.single j 1 = Q j j := by
    simp [dotProduct,Matrix.vecMul,Pi.single_apply,ite_mul,mul_ite]
  rw [hdiag,dotProduct_comm]
  rfl

theorem logGram_rectLevi_singleColumn {n m : ℕ} (M : Rect n m)
    (hM : (M*Mᴴ).PosDef) (j : Fin m) (V : ComplexVector n) :
    rectLevi logGram M (singleColumn j V) =
      (1-(rowProjector M j j).re)*qform ((M*Mᴴ)⁻¹) V := by
  rw [logGram_rectLevi_formula M _ hM,trace_singleColumn]
  have him : (rowProjector M j j).im = 0 :=
    (RCLike.nonneg_iff.mp ((rowProjector_posSemidef M hM).diag_nonneg (i := j))).2
  simp only [Complex.mul_re,qform,Matrix.sub_apply,Matrix.one_apply_eq,
    Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,him,sub_zero,zero_mul]

end Yau.NodeProofs.E02Aux
