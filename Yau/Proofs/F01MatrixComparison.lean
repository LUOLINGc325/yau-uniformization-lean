import Yau.Proofs.F01MatrixCoercivity

/-! Quadratic bounds imply the exact positive-semidefinite matrix sandwich
used by the original bounded-geometry contract. -/
open Matrix
open scoped ComplexOrder
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_quadratic_im_zero {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ (H *ᵥ v)).im = 0 := by
  have h := congrArg Complex.im (hH.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem euclidean_quadratic_identity (v : EuclideanSpace ℂ ι) :
    star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  convert! h using 1
  norm_cast

theorem matrix_sandwich_of_quadratic_bounds {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {ℓ C D : ℝ} (hD : 0 < D) (hDl : D⁻¹ ≤ ℓ) (hDC : C ≤ D)
    (hb : ∀ v : EuclideanSpace ℂ ι,
      ℓ * ‖v‖ ^ 2 ≤ (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re ∧
      (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re ≤ C * ‖v‖ ^ 2) :
    (H - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧ ((D : ℂ) • 1 - H).PosSemidef := by
  have hs (a : ℝ) : (((a : ℂ) • (1 : Matrix ι ι ℂ))).IsHermitian :=
    Matrix.isHermitian_one.smul (show IsSelfAdjoint (a : ℂ) from Complex.conj_ofReal a)
  constructor
  · have hh := hH.sub (hs D⁻¹)
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hermitian_quadratic_im_zero hh v).symm⟩
    have hv := (hb (WithLp.toLp 2 v)).1
    have hid := euclidean_quadratic_identity (WithLp.toLp 2 v)
    simp only [WithLp.ofLp_toLp] at hv hid
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, hid, smul_eq_mul, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_right hDl (sq_nonneg ‖WithLp.toLp 2 v‖)]
  · have hh := (hs D).sub hH
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hermitian_quadratic_im_zero hh v).symm⟩
    have hv := (hb (WithLp.toLp 2 v)).2
    have hid := euclidean_quadratic_identity (WithLp.toLp 2 v)
    simp only [WithLp.ofLp_toLp] at hv hid
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, hid, smul_eq_mul, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_right hDC (sq_nonneg ‖WithLp.toLp 2 v‖)]

theorem compact_posDef_matrix_sandwich {A : Type*} [TopologicalSpace A]
    {K : Set A} (hK : IsCompact K) {G : A → Matrix ι ι ℂ}
    (hG : ContinuousOn G K) (hpos : ∀ a ∈ K, (G a).PosDef) :
    ∃ D : ℝ, 0 < D ∧ ∀ a ∈ K,
      (G a - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧ ((D : ℂ) • 1 - G a).PosSemidef := by
  obtain ⟨ℓ, C, hℓ, hC, hb⟩ := compact_posDef_quadratic_bounds hK hG hpos
  let D := max 1 (max C ℓ⁻¹) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hDC : C ≤ D := by dsimp [D]; linarith [le_max_left C ℓ⁻¹, le_max_right (1 : ℝ) (max C ℓ⁻¹)]
  have hDl' : ℓ⁻¹ ≤ D := by dsimp [D]; linarith [le_max_right C ℓ⁻¹, le_max_right (1 : ℝ) (max C ℓ⁻¹)]
  have hDl : D⁻¹ ≤ ℓ := by
    simpa only [inv_inv] using (inv_le_inv₀ hD (inv_pos.mpr hℓ)).mpr hDl'
  exact ⟨D, hD, fun a ha => matrix_sandwich_of_quadratic_bounds (hpos a ha).1 hD hDl hDC (hb a ha)⟩

end Yau.NodeProofs.F01Aux
