import Yau.Proofs.P04LeviLogChain

noncomputable section
open WithLp
open scoped Topology InnerProductSpace Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

def radialRankOne (w : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => w i * star (w j)

theorem radialRankOne_posSemidef (w : ComplexVector n) : (radialRankOne w).PosSemidef := by
  let B : Matrix (Fin 1) (Fin n) ℂ := fun _ j => star (w j)
  convert Matrix.posSemidef_conjTranspose_mul_self B using 1
  ext i j
  change w i * star (w j) = ∑ k : Fin 1, star (B k i)*B k j
  simp [B]

theorem radialRankOne_quadratic (w : ComplexVector n) (x : Fin n → ℂ) :
    star x ⬝ᵥ ((radialRankOne w) *ᵥ x) =
      ⟪(toLp 2 x : ComplexVector n),w⟫_ℂ * ⟪w,(toLp 2 x : ComplexVector n)⟫_ℂ := by
  simp only [radialRankOne,Matrix.mulVec,dotProduct,Pi.star_apply,
    EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The radial Cauchy--Schwarz matrix estimate, including dimension zero. -/
theorem radial_cauchy_matrix (w : ComplexVector n) :
    (((‖w‖^2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-radialRankOne w).PosSemidef := by
  have hHerm := ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosSemidef).smul
    (sq_nonneg ‖w‖)).isHermitian.sub (radialRankOne_posSemidef w).isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro x
  let X : ComplexVector n := toLp 2 x
  have hself : star x ⬝ᵥ x = ((‖X‖^2 : ℝ) : ℂ) := by
    calc
      _ = ⟪X,X⟫_ℂ := by simp only [X,EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,dotProduct_comm]
      _ = (‖X‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K X
      _ = _ := by push_cast; rfl
  have hprod : ⟪X,w⟫_ℂ * ⟪w,X⟫_ℂ = ((‖⟪w,X⟫_ℂ‖^2 : ℝ) : ℂ) := by
    calc
      _ = star (⟪w,X⟫_ℂ) * ⟪w,X⟫_ℂ :=
        congrArg (fun t => t*⟪w,X⟫_ℂ) (inner_conj_symm X w).symm
      _ = (‖⟪w,X⟫_ℂ‖ : ℂ)^2 := RCLike.conj_mul _
      _ = _ := by push_cast; rfl
  rw [Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,hself,radialRankOne_quadratic,hprod]
  have HH := norm_inner_le_norm (𝕜 := ℂ) w X
  have HR : 0 ≤ ‖w‖^2*‖X‖^2-‖⟪w,X⟫_ℂ‖^2 := by
    nlinarith [norm_nonneg w,norm_nonneg X,norm_nonneg (⟪w,X⟫_ℂ)]
  simpa only [smul_eq_mul,Complex.real_smul,← Complex.ofReal_mul,← Complex.ofReal_sub] using
    (Complex.zero_le_real.mpr HR)

end Yau.Proofs.P04Aux
