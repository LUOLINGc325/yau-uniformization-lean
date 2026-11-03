import Yau.Proofs.Y06FiniteStages
import Yau.Proofs.Y06SizeAlgebra

/-! Horizon-independent estimates for the actual homogeneous forcing and
finite backward correction. All exponents precede the choice of a late mask. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d m : ℕ}

theorem exp_next_size {P : PolyMap n} {E x y L : ℝ}
    (hE : 0 ≤ E) (hx : 1 ≤ x) (hL : 0 ≤ L) (hstep : y ≤ x + L)
    (hP : polySize P ≤ Real.exp (E * y)) :
    polySize P ≤ Real.exp ((E * (1 + L)) * x) := by
  apply hP.trans (Real.exp_le_exp.mpr _)
  have hnext : y ≤ (1 + L) * x := by nlinarith
  nlinarith

theorem stageDiscrepancy_size (P H G : ℕ → PolyMap n) (J : ℕ → Herm n)
    (k m : ℕ) {A E L x : ℝ}
    (hHdegree : (H (k + 1)).degree ≤ d) (hGdegree : (G k).degree ≤ d)
    (hP : polySize (P k) ≤ Real.exp (A * x))
    (hJ : polySize (linearPolynomial (J k)) ≤ Real.exp (A * x))
    (hJi : polySize (linearPolynomial (J k)⁻¹) ≤ Real.exp (A * x))
    (hH : polySize (H k) ≤ Real.exp (E * x))
    (hHnext : polySize (H (k + 1)) ≤ Real.exp ((E * (1 + L)) * x))
    (hG : polySize (G k) ≤ Real.exp (E * x)) :
    polySize (stageDiscrepancy m P H G J k) ≤
      Real.exp ((((d : ℝ) + 2 + L) * E + (2 * (d : ℝ) + 1) * A) * x) := by
  have hJP := polySize_exp_comp (linearPoly_degree_le (J k)) hJ hP
  have hHJP := polySize_exp_comp hHdegree hHnext hJP
  have hR := polySize_exp_comp (linearPoly_degree_le (J k)⁻¹) hJi hHJP
  have hGH := polySize_exp_comp hGdegree hG hH
  have hB := (polySize_homogeneousPart m _).trans (polySize_exp_sub hR hGH)
  change polySize (homogeneousPart m (layerRight P H J k - (G k).comp (H k))) ≤ _
  convert hB using 1 <;> congr 1 <;> push_cast <;> ring

theorem projected_forcing_size (D : Herm n) (w : Fin n → ℝ) (B : PolyMap n) {A F x : ℝ}
    (hD : polySize (linearPolynomial D⁻¹) ≤ Real.exp (A * x))
    (hB : polySize B ≤ Real.exp (F * x)) :
    polySize (forbiddenProjection w ((linearPolynomial D⁻¹).comp B)) ≤ Real.exp ((A + F) * x) := by
  exact (polySize_forbiddenProjection _ _).trans (by
    simpa only [Nat.cast_one, one_mul, linearPolynomial_as_linearPoly] using
      polySize_exp_comp (linearPoly_degree_le D⁻¹) hD hB)

theorem exp_gap_half {x F : ℝ} (hx : 1 ≤ x) :
    Real.exp (F * x) ≤ Real.exp ((F + 1) * x) / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp x := by have := Real.add_one_le_exp x; linarith
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ Real.exp (F * x) * Real.exp x := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem weighted_exp_step_half {a H x y L : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hstep : y ≤ x + L)
    (hsmall : a * Real.exp (H * L) ≤ 1 / 2) :
    a * Real.exp (H * y) ≤ Real.exp (H * x) / 2 := by
  calc
    _ ≤ a * Real.exp (H * (x + L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hstep hH)) ha
    _ = (a * Real.exp (H * L)) * Real.exp (H * x) := by
      rw [mul_add, Real.exp_add]; ring
    _ ≤ (1 / 2) * Real.exp (H * x) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = _ := by ring

theorem finiteLayerCorrection_coeff_envelope (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n)
    (hB : ∀ k, Homogeneous (B k) m) (x a : ℕ → ℝ) {F L : ℝ}
    (hx : ∀ k, 1 ≤ x k) (ha : ∀ k, 0 ≤ a k) (hF : 0 ≤ F + 1)
    (hstep : ∀ k, active k → x (k + 1) ≤ x k + L)
    (hT : ∀ k, active k → ∀ X : PolyMap n, Homogeneous X m →
      (backwardOperator (D k) (J k) (w k) X).coeffNorm ≤ a k * X.coeffNorm)
    (hforce : ∀ k, active k →
      (forbiddenProjection (w k) ((linearPolynomial (D k)⁻¹).comp (B k))).coeffNorm ≤ Real.exp (F * x k))
    (hsmall : ∀ k, active k → a k * Real.exp ((F + 1) * L) ≤ 1 / 2) :
    ∀ k, (finiteLayerCorrection b active D J w B k).coeffNorm ≤ Real.exp ((F + 1) * x k) := by
  let u := finiteLayerCorrection b active D J w B
  have hu : ∀ k, Homogeneous (u k) m := finiteLayerCorrection_homogeneous b active D J w B hB
  have hzero (k : ℕ) (h : u k = 0) : (u k).coeffNorm ≤ Real.exp ((F + 1) * x k) := by
    rw [h]
    simpa only [PolyMap.coeffNorm, Pi.zero_apply, MvPolynomial.support_zero, Finset.sum_empty,
      Finset.sum_const_zero] using (Real.exp_pos ((F + 1) * x k)).le
  have hbelow : ∀ k, k ≤ b → (u k).coeffNorm ≤ Real.exp ((F + 1) * x k) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => exact hzero b (finiteLayerCorrection_terminal b active D J w B le_rfl)
    | of_succ k hk ih =>
      by_cases hact : active k
      · change (u k).coeffNorm ≤ _
        have hrec : u k = backwardAffineStep (D k) (J k) (w k) (B k) (u (k + 1)) :=
          finiteLayerCorrection_step b active D J w B hk hact
        rw [hrec]
        have hbound := backwardAffineStep_coeffNorm_bound (D k) (J k) (w k) (B k) (u (k + 1))
          (hT k hact _ (hu (k + 1))) (hforce k hact)
        have hterm := (mul_le_mul_of_nonneg_left ih (ha k)).trans
          (weighted_exp_step_half (ha k) hF (hstep k hact) (hsmall k hact))
        linarith [exp_gap_half (F := F) (hx k)]
      · exact hzero k (finiteLayerCorrection_inactive b active D J w B hact)
  intro k
  by_cases hk : k ≤ b
  · exact hbelow k hk
  · exact hzero k (finiteLayerCorrection_terminal b active D J w B (by omega))

end Yau.Proofs.Y06Aux
