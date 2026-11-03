import Yau.Proofs.F01ComplexHeatRealification
import Yau.LeafProofs.L17ScalarEllipticity

/-! The canonical L17 principal symbol satisfies the full original L16
real ellipticity predicate. Its constants precede every coefficient field. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem complexHeatCoefficient_eq_scalarSymbol (H : Matrix (Fin n) (Fin n) ℂ) :
    complexHeatCoefficient H = scalarSymbol H := rfl

theorem scalarSymbol_isSymm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (scalarSymbol H).IsSymm := by
  ext i j
  simpa only [star_trivial, Matrix.transpose_apply] using (scalarSymbol_posDef hH).isHermitian.apply i j

theorem real_matrix_sandwich_quadratic {A : Mat n} {ell upper : ℝ}
    (hlo : (A - ell • 1).PosSemidef) (hhi : (upper • 1 - A).PosSemidef)
    (v : RIdx n → ℝ) :
    ell * (∑ i, (v i) ^ 2) ≤ ∑ i, ∑ j, A i j * v i * v j ∧
      (∑ i, ∑ j, A i j * v i * v j) ≤ upper * (∑ i, (v i) ^ 2) := by
  have hl := hlo.dotProduct_mulVec_nonneg v
  have hh := hhi.dotProduct_mulVec_nonneg v
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, star_trivial] at hl hh
  have hself : v ⬝ᵥ v = ∑ i, (v i) ^ 2 := by simp only [dotProduct, pow_two]
  have hprod : v ⬝ᵥ (A *ᵥ v) = ∑ i, ∑ j, A i j * v i * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hself, hprod] at hl hh
  exact ⟨by linarith, by linarith⟩

theorem scalarSymbol_elliptic_of_uniform_sandwich
    {H : Point n → Matrix (Fin n) (Fin n) ℂ} {Q : Set (Point n)} {D : ℝ}
    (hD : 1 ≤ D) (hpos : ∀ p ∈ Q, (H p).PosDef)
    (hbound : ∀ p ∈ Q,
      (H p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧ ((D : ℂ) • 1 - H p).PosSemidef) :
    Elliptic Q (fun p => scalarSymbol (H p)) ((4 * D)⁻¹) (D / 4) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hi : D⁻¹ ≤ D := by
    have h1 : D⁻¹ ≤ (1 : ℝ) := by
      simpa only [inv_one] using (inv_le_inv₀ hDpos zero_lt_one).mpr hD
    exact h1.trans hD
  refine ⟨inv_pos.mpr (by positivity), ?_, ?_⟩
  · calc
      (4 * D)⁻¹ = (1 / 4 : ℝ) * D⁻¹ := by rw [mul_inv_rev]; ring
      _ ≤ (1 / 4 : ℝ) * D := mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = D / 4 := by ring
  · intro p hp
    refine ⟨scalarSymbol_isSymm (hpos p hp), ?_⟩
    intro v
    have hb := Yau.LeafProofs.L17Aux.scalarSymbol_ellipticity
      (hpos p hp) hDpos (hbound p hp).1 (hbound p hp).2
    exact real_matrix_sandwich_quadratic hb.1 hb.2 v

end Yau.NodeProofs.F01Aux
