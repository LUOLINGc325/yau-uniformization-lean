import Yau.LeafProofs.L17ScalarEllipticity
import Yau.LeafProofs.L16

/-! Actual uniformly controlled Gaussian coordinate equivalences for the frozen scalar symbol. -/

noncomputable section

open scoped Matrix

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem real_matrix_quadratic_eq {ι : Type*} [Fintype ι]
    (a : Matrix ι ι ℝ) (v : ι → ℝ) :
    star v ⬝ᵥ (a *ᵥ v) = ∑ i, ∑ j, a i j * v i * v j := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem real_matrix_lower_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Matrix ι ι ℝ) (lam : ℝ) (h : (a - lam • 1).PosSemidef) (v : ι → ℝ) :
    lam * (∑ i, (v i)^2) ≤ ∑ i, ∑ j, a i j * v i * v j := by
  have hb := h.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, real_matrix_quadratic_eq] at hb
  have hv : star v ⬝ᵥ v = ∑ i, (v i)^2 := by
    simp only [dotProduct, Pi.star_apply, star_trivial, pow_two]
  rw [hv] at hb
  simp only [smul_eq_mul] at hb
  linarith

theorem real_matrix_upper_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Matrix ι ι ℝ) (upper : ℝ) (h : (upper • 1 - a).PosSemidef) (v : ι → ℝ) :
    (∑ i, ∑ j, a i j * v i * v j) ≤ upper * (∑ i, (v i)^2) := by
  have hb := h.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, real_matrix_quadratic_eq] at hb
  have hv : star v ⬝ᵥ v = ∑ i, (v i)^2 := by
    simp only [dotProduct, Pi.star_apply, star_trivial, pow_two]
  rw [hv] at hb
  simp only [smul_eq_mul] at hb
  linarith

def BoundedChartFamily.frozenEllipticLower (A : BoundedChartFamily g) : ℝ :=
  (4 * A.bound 0)⁻¹

def BoundedChartFamily.frozenEllipticUpper (A : BoundedChartFamily g) : ℝ :=
  max A.frozenEllipticLower (A.bound 0 / 4)

theorem BoundedChartFamily.frozenEllipticLower_pos (A : BoundedChartFamily g) :
    0 < A.frozenEllipticLower := by
  have := A.bound_pos 0
  dsimp [BoundedChartFamily.frozenEllipticLower]
  positivity

theorem BoundedChartFamily.exists_frozen_heat_equivalences (A : BoundedChartFamily g) :
    ∃ B : M.Carrier → ComplexVector n ≃L[ℝ] ComplexVector n,
      (∀ p, ‖(B p : ComplexVector n →L[ℝ] ComplexVector n)‖ ≤
          Real.sqrt A.frozenEllipticUpper ∧
        ‖((B p).symm : ComplexVector n →L[ℝ] ComplexVector n)‖ ≤
          (Real.sqrt A.frozenEllipticLower)⁻¹) ∧
      ∀ p (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ),
        (∑ k : RIdx n, H (B p (realVec k)) (B p (realVec k))) =
          ∑ i : RIdx n, ∑ j : RIdx n,
            scalarSymbol (pullbackMatrix g (A.chart p) 0) i j * H (realVec i) (realVec j) := by
  have hlam := A.frozenEllipticLower_pos
  have hupper : A.frozenEllipticLower ≤ A.frozenEllipticUpper := le_max_left _ _
  have hpoint (p : M.Carrier) :
      ∃ B : ComplexVector n ≃L[ℝ] ComplexVector n,
        ‖(B : ComplexVector n →L[ℝ] ComplexVector n)‖ ≤ Real.sqrt A.frozenEllipticUpper ∧
        ‖(B.symm : ComplexVector n →L[ℝ] ComplexVector n)‖ ≤
          (Real.sqrt A.frozenEllipticLower)⁻¹ ∧
        ∀ H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ,
          (∑ k : RIdx n, H (B (realVec k)) (B (realVec k))) =
            ∑ i : RIdx n, ∑ j : RIdx n,
              scalarSymbol (pullbackMatrix g (A.chart p) 0) i j * H (realVec i) (realVec j) := by
    have hz : (0 : ComplexVector n) ∈ Metric.ball 0 A.radius := Metric.mem_ball_self A.radius_pos
    have hzs := A.closedBall_source p (Metric.ball_subset_closedBall hz)
    have hpos := scalarSymbol_posDef
      (pullbackMatrix_posDef g (A.chart p) (A.differentiable p) (A.inverse_differentiable p) hzs)
    have hell := A.scalarSymbol_ellipticity p hz
    apply L16Aux.elliptic_matrix_space_equiv _ hlam hupper hpos.isHermitian.isSymm
    intro v
    refine ⟨real_matrix_lower_form _ _ hell.1 v, ?_⟩
    exact (real_matrix_upper_form _ _ hell.2 v).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  choose B hBN hBI hGram using hpoint
  exact ⟨B, fun p => ⟨hBN p, hBI p⟩, hGram⟩

end Yau.LeafProofs.L17Aux
