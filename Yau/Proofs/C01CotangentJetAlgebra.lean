import Yau.Proofs.C01InverseJetAlgebra
import Yau.Proofs.Y03DualPullback

/-! Exact transpose conventions and cancellation of the free holomorphic
cotangent jet.  These are finite matrix identities, not additional geometric
or Harnack premises for the original C01 statement. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem dualNormMat_eq_conjugate_quadratic (H : Herm n) (ξ : Fin n → ℂ) :
    dualNormMat H (WithLp.toLp 2 ξ) =
      (star (star ξ) ⬝ᵥ (H⁻¹ *ᵥ star ξ)).re := by
  unfold dualNormMat
  simp only [WithLp.ofLp_toLp, star_star]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.star_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dualNormMat_coe_eq_conjugate_quadratic
    (H : Herm n) (hH : H.IsHermitian) (ξ : Fin n → ℂ) :
    (dualNormMat H (WithLp.toLp 2 ξ) : ℂ) =
      star (star ξ) ⬝ᵥ (H⁻¹ *ᵥ star ξ) := by
  apply Complex.ext
  · exact dualNormMat_eq_conjugate_quadratic H ξ
  · simpa only [Complex.ofReal_im, RCLike.im_to_complex] using
      (hH.inv.im_star_dotProduct_mulVec_self (star ξ)).symm

/-- For the freely chosen cotangent first derivative, its last two
quadratic terms cancel.  No commutation of first metric jets is used. -/
theorem free_jet_quadratic_elimination
    (H K₁ K₂ K₁₂ : Herm n) (hH : IsUnit H.det) (a : Fin n → ℂ) :
    let b := -(H *ᵥ (K₂ *ᵥ a))
    star a ⬝ᵥ (K₁₂ *ᵥ a) + star b ⬝ᵥ (K₂ *ᵥ a) +
      star a ⬝ᵥ (K₁ *ᵥ b) + star b ⬝ᵥ (H⁻¹ *ᵥ b) =
        star a ⬝ᵥ ((K₁₂ - K₁ * H * K₂) *ᵥ a) := by
  dsimp only
  have hcancel : H⁻¹ *ᵥ (-(H *ᵥ (K₂ *ᵥ a))) = -(K₂ *ᵥ a) := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hH,
      Matrix.one_mulVec]
  have hthird : star a ⬝ᵥ (K₁ *ᵥ (-(H *ᵥ (K₂ *ᵥ a)))) =
      -(star a ⬝ᵥ ((K₁ * H * K₂) *ᵥ a)) := by
    rw [Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  rw [hcancel, hthird, dotProduct_neg, Matrix.sub_mulVec, dotProduct_sub]
  have hscalar (x y z : ℂ) : x + y + -z + -y = x - z := by ring
  exact hscalar _ _ _

theorem inverse_metric_quadratic_cancel (H C : Herm n)
    (hH : H.IsHermitian) (hunit : IsUnit H.det) (v : Fin n → ℂ) :
    star (H *ᵥ v) ⬝ᵥ ((H⁻¹ * C * H⁻¹) *ᵥ (H *ᵥ v)) =
      star v ⬝ᵥ (C *ᵥ v) := by
  rw [Alignment.Y03Proof.conjugate_quadratic]
  have hconj : Hᴴ * (H⁻¹ * C * H⁻¹) * H = C := by
    rw [hH.eq]
    calc
      H * (H⁻¹ * C * H⁻¹) * H = (H * H⁻¹) * C * (H⁻¹ * H) := by noncomm_ring
      _ = C := by
        rw [Matrix.mul_nonsing_inv H hunit, Matrix.nonsing_inv_mul H hunit,
          Matrix.one_mul, Matrix.mul_one]
  rw [hconj]

/-- The Schur remainder of the actual cometric jet gives positivity of the
tangent curvature.  In C01, the product identities and free-jet inequality
are computed from the same joint dual norm supplied by E03. -/
theorem curvature_posSemidef_of_free_jet
    (H K₁ K₂ K₁₂ C : Herm n) (hH : H.PosDef) (hC : C.IsHermitian)
    (hschur : K₁₂ - K₁ * H * K₂ = H⁻¹ * C * H⁻¹)
    (hjet : ∀ a b : Fin n → ℂ,
      0 ≤ (star a ⬝ᵥ (K₁₂ *ᵥ a) + star b ⬝ᵥ (K₂ *ᵥ a) +
        star a ⬝ᵥ (K₁ *ᵥ b) + star b ⬝ᵥ (H⁻¹ *ᵥ b)).re) :
    C.PosSemidef := by
  have hunit : IsUnit H.det := hH.isUnit.map Matrix.detMonoidHom
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hC
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hC.im_star_dotProduct_mulVec_self v).symm⟩
  have hpos := hjet (H *ᵥ v) (-(H *ᵥ (K₂ *ᵥ (H *ᵥ v))))
  rw [free_jet_quadratic_elimination H K₁ K₂ K₁₂ hunit, hschur,
    inverse_metric_quadratic_cancel H C hH.isHermitian hunit] at hpos
  exact hpos

end Yau.NodeProofs.C01Aux
