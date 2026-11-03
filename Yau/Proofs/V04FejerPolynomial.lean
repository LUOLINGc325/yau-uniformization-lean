import Yau.Blueprint.VariationContracts

/-! The frozen Fejér columns are polynomials with strictly positive
exponents. Their boundary frequency shift retains every negative mode. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem fejer_exponent_pos {P : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ)) :
    0 < (k + (P : ℤ) + 1).toNat := by
  have := (Finset.mem_Icc.mp hk).1
  omega

theorem fejer_exponent_le {P : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ)) :
    (k + (P : ℤ) + 1).toNat ≤ 2 * P + 1 := by
  have := (Finset.mem_Icc.mp hk).2
  omega

theorem fejerTestColumn_holomorphic (d : VariationData X q) (j a : ℕ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (P : ℕ)
    (i : CotangentIndex n) : HolomorphicColumn (fejerTestColumn d j a F E P i) := by
  intro r
  unfold fejerTestColumn
  fun_prop

theorem fejerTestColumn_zero (d : VariationData X q) (j a : ℕ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (P : ℕ)
    (i : CotangentIndex n) : fejerTestColumn d j a F E P i 0 = 0 := by
  funext r
  apply Finset.sum_eq_zero
  intro k hk
  simp only [zero_pow (fejer_exponent_pos hk).ne', mul_zero]

theorem fejer_mode_boundary (θ : ℝ) {P : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ)) :
    circlePoint θ ^ (k + (P : ℤ) + 1).toNat =
      circlePoint θ ^ (P + 1) * Complex.exp ((k : ℂ) * θ * Complex.I) := by
  have hnonneg : 0 ≤ k + (P : ℤ) + 1 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hcast : (((k + (P : ℤ) + 1).toNat : ℕ) : ℂ) =
      (k : ℂ) + (P : ℂ) + 1 := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  unfold circlePoint
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, hcast]
  congr 1
  push_cast
  ring

theorem fejerMean_apply (A : ℝ → CotangentMatrix n) (P : ℕ) (θ : ℝ)
    (r i : CotangentIndex n) :
    fejerMean A P θ r i = ∑ k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
      (((1 - |(k : ℝ)| / (P + 1)) : ℂ) *
        Complex.exp ((k : ℂ) * θ * Complex.I)) * circleFourier (fun t => A t r i) k := by
  unfold fejerMean
  exact (Matrix.sum_apply r i _ _).trans (Finset.sum_congr rfl (fun k _ => rfl))

/-- The shift has exactly modulus one, while the polynomial remains the
actual column used in the original Fejér test. -/
theorem fejerTestColumn_boundary (d : VariationData X q) (j a : ℕ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (P : ℕ)
    (i r : CotangentIndex n) (θ : ℝ) :
    fejerTestColumn d j a F E P i (circlePoint θ) r =
      circlePoint θ ^ (P + 1) *
        fejerMean (fun t => matrixNegative (boundarySymbol d j a F E (circlePoint t)))
          P θ r i := by
  rw [fejerMean_apply]
  unfold fejerTestColumn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fejer_mode_boundary θ hk]
  ring

end Yau.Blueprint.V04Proof
