import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Finite algebra for the nonnegative bisectional cone. Its scalar trace
vanishes only for the zero tensor; no geometric realization is assumed. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

theorem matrix_eq_zero_of_quadratic_zero (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ v : Fin n → ℂ, star v ⬝ᵥ (A *ᵥ v) = 0) : A = 0 := by
  have hLin : A.toEuclideanLin = 0 := by
    apply (inner_map_self_eq_zero A.toEuclideanLin).mp
    intro v
    apply inner_eq_zero_symm.mp
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, WithLp.ofLp_toLp, dotProduct_comm] using hA (WithLp.ofLp v)
  exact Matrix.toEuclideanLin.injective (hLin.trans (map_zero Matrix.toEuclideanLin).symm)

abbrev CurvatureArray (n : ℕ) := Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ

def curvaturePartial (C : CurvatureArray n) (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ k, ∑ l, star (v k) * C i j k l * v l

def curvatureRicciPartial (C : CurvatureArray n) : Matrix (Fin n) (Fin n) ℂ :=
  fun k l => ∑ i, C i i k l

theorem trace_curvaturePartial (C : CurvatureArray n) (v : Fin n → ℂ) :
    (curvaturePartial C v).trace = star v ⬝ᵥ (curvatureRicciPartial C *ᵥ v) := by
  simp only [curvaturePartial, curvatureRicciPartial, Matrix.trace, Matrix.diag,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem curvatureRicciPartial_posSemidef (C : CurvatureArray n)
    (hC : ∀ i j k l, star (C j i l k) = C i j k l)
    (hP : ∀ v, (curvaturePartial C v).PosSemidef) :
    (curvatureRicciPartial C).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro k l
    simp only [curvatureRicciPartial, star_sum]
    exact Finset.sum_congr rfl (fun i _ => hC i i k l)
  · intro v
    rw [← trace_curvaturePartial]
    exact (hP v).trace_nonneg

theorem curvatureArray_eq_zero_of_trace_zero (C : CurvatureArray n)
    (hC : ∀ i j k l, star (C j i l k) = C i j k l)
    (hP : ∀ v, (curvaturePartial C v).PosSemidef)
    (hTrace : (curvatureRicciPartial C).trace = 0) : C = 0 := by
  have hR : curvatureRicciPartial C = 0 :=
    (curvatureRicciPartial_posSemidef C hC hP).trace_eq_zero_iff.mp hTrace
  have hPartial (v : Fin n → ℂ) : curvaturePartial C v = 0 := by
    apply (hP v).trace_eq_zero_iff.mp
    rw [trace_curvaturePartial, hR]
    simp
  have hEntry (i j : Fin n) : C i j = 0 := by
    apply matrix_eq_zero_of_quadratic_zero
    intro v
    have hv := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) (hPartial v)
    simpa only [curvaturePartial, Matrix.zero_apply, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.mul_sum, mul_assoc] using hv
  ext i j k l
  exact congrFun (congrFun (hEntry i j) k) l

end Yau.Blueprint.C02Proof
