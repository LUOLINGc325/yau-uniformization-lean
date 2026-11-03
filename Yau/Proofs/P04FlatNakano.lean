import Yau.Proofs.P04TrivialLine

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem nakano_line_quadratic (L : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin n → Fin 1 → ℂ) :
    BundleDbar.nakanoQuadratic
      (fun i j => L j i • (1 : Matrix (Fin 1) (Fin 1) ℂ)) U =
      (star (fun i => U i 0) ⬝ᵥ (L *ᵥ (fun i => U i 0))).re := by
  simp only [BundleDbar.nakanoQuadratic,Matrix.smul_apply,Matrix.one_apply,
    Fintype.sum_unique,ite_true,mul_one,smul_eq_mul,Matrix.mulVec,dotProduct,
    Pi.star_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hd : (default : Fin 1)=0 := Subsingleton.elim _ _
  rw [hd]
  ring

/-- The transposed derivative indices in the actual weighted bundle curvature
produce exactly the ordinary positive Levi quadratic form. -/
theorem flat_weightedNakano_of_chartLevi (φ : M.Carrier → ℝ)
    (hφ : ∀ a z, z ∈ chartTarget a → (leviC (inChart a φ) z).PosSemidef) :
    BundleDbar.WeightedNakanoNonnegative (r := 1) (CanonicalCoefficients M) flatMetric φ := by
  intro a z hz U
  have hz' : z ∈ chartTarget a := by
    rwa [coefficient_localDomain] at hz
  have heq : BundleDbar.weightedCurvature (r := 1) (CanonicalCoefficients M) flatMetric φ a z =
      fun i j => leviC (inChart a φ) z j i • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    funext i j
    simp only [BundleDbar.weightedCurvature,flat_curvature,flat_metricMatrix,zero_add]
  rw [heq,nakano_line_quadratic]
  exact (Complex.nonneg_iff.mp ((hφ a z hz').dotProduct_mulVec_nonneg (fun i => U i 0))).1

end Yau.Proofs.P04Aux
