import spec.CHAIN.CONTRACTS

/-! Uncompiled F01 scratch: actual congruence invariance of the Rayleigh
quotient. Global smoothness is proved in fixed charts, never by assuming that
the native center-dependent gMat frame varies continuously with its center. -/
open scoped Matrix ComplexOrder
open Matrix Set
noncomputable section
namespace Yau.NodeProofs.F01Aux

variable {ι : Type*} [Fintype ι]

def matrixQuadraticValue (H : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ (H *ᵥ v)).re

def matrixRayleigh (H K : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  matrixQuadraticValue K v / matrixQuadraticValue H v

theorem matrixQuadraticValue_congruence (A H : Matrix ι ι ℂ) (v : ι → ℂ) :
    matrixQuadraticValue (Aᴴ * H * A) v = matrixQuadraticValue H (A *ᵥ v) := by
  unfold matrixQuadraticValue
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem matrixRayleigh_congruence (A H K : Matrix ι ι ℂ) (v : ι → ℂ) :
    matrixRayleigh (Aᴴ * H * A) (Aᴴ * K * A) v =
      matrixRayleigh H K (A *ᵥ v) := by
  unfold matrixRayleigh
  rw [matrixQuadraticValue_congruence, matrixQuadraticValue_congruence]

theorem matrixRayleigh_range_congruence (A H K : Matrix ι ι ℂ)
    (hA : Function.Surjective (fun v => A *ᵥ v)) :
    range (matrixRayleigh (Aᴴ * H * A) (Aᴴ * K * A)) = range (matrixRayleigh H K) := by
  ext q
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨A *ᵥ v, (matrixRayleigh_congruence A H K v).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := hA v
    exact ⟨w, (matrixRayleigh_congruence A H K w).trans (congrArg _ hw)⟩

end Yau.NodeProofs.F01Aux
