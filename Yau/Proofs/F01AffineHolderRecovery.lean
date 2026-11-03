import Yau.Proofs.F01AffineParabolicHolder

/-! Numerical Holder estimates pull back under arbitrary affine
parabolic dilations, with an explicit scale budget. The inverse map
recovers estimates in the original coordinates. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

def affineHolderScale (ρ β : ℝ) : ℝ := max (|ρ| ^ β) ((ρ ^ 2) ^ (β / 2))

theorem affineHolderScale_nonneg (ρ β : ℝ) : 0 ≤ affineHolderScale ρ β := by
  exact le_max_of_le_left (Real.rpow_nonneg (abs_nonneg _) _)

theorem holderWeight_affineParabolicPoint_general (ρ β : ℝ)
    (c : Space n) (τ : ℝ) (p q : Point n) :
    holderWeight β (affineParabolicPoint ρ c τ p) (affineParabolicPoint ρ c τ q) ≤
      affineHolderScale ρ β * holderWeight β p q := by
  have hSpace : ‖(affineParabolicPoint ρ c τ p).1 -
      (affineParabolicPoint ρ c τ q).1‖ = |ρ| * ‖p.1 - q.1‖ := by
    change ‖ρ • p.1 + c - (ρ • q.1 + c)‖ = _
    have he : ρ • p.1 + c - (ρ • q.1 + c) = ρ • (p.1 - q.1) := by
      rw [smul_sub]; abel
    rw [he, norm_smul, Real.norm_eq_abs]
  have hTime : |(affineParabolicPoint ρ c τ p).2 -
      (affineParabolicPoint ρ c τ q).2| = ρ ^ 2 * |p.2 - q.2| := by
    change |τ + ρ ^ 2 * p.2 - (τ + ρ ^ 2 * q.2)| = _
    have he : τ + ρ ^ 2 * p.2 - (τ + ρ ^ 2 * q.2) = ρ ^ 2 * (p.2 - q.2) := by ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  unfold holderWeight
  rw [hSpace, hTime, Real.mul_rpow (abs_nonneg _) (norm_nonneg _),
    Real.mul_rpow (sq_nonneg _) (abs_nonneg _), mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

theorem holderBound_affine_general {Q Q' : Set (Point n)} {β C ρ : ℝ}
    {c : Space n} {τ : ℝ} {f : Point n → E}
    (hMap : MapsTo (affineParabolicPoint ρ c τ) Q' Q) (hf : HolderBound β Q f C) :
    HolderBound β Q' (fun p => f (affineParabolicPoint ρ c τ p))
      ((1 + affineHolderScale ρ β) * C) := by
  have hK := affineHolderScale_nonneg ρ β
  refine ⟨mul_nonneg (by positivity) hf.1, ?_, ?_⟩
  · intro p hp
    exact (hf.2.1 _ (hMap hp)).trans (by nlinarith [hf.1, mul_nonneg hK hf.1])
  · intro p hp q hq
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    calc
      _ ≤ C * holderWeight β (affineParabolicPoint ρ c τ p)
          (affineParabolicPoint ρ c τ q) := hf.2.2 _ (hMap hp) _ (hMap hq)
      _ ≤ C * (affineHolderScale ρ β * holderWeight β p q) :=
        mul_le_mul_of_nonneg_left (holderWeight_affineParabolicPoint_general ρ β c τ p q) hf.1
      _ ≤ ((1 + affineHolderScale ρ β) * C) * holderWeight β p q := by
        nlinarith [mul_nonneg hf.1 hw]

theorem affineParabolicPoint_inverse_right {ρ : ℝ} (hρ : ρ ≠ 0)
    (c : Space n) (τ : ℝ) (p : Point n) :
    affineParabolicPoint ρ c τ
      (affineParabolicPoint ρ⁻¹ (-(ρ⁻¹ • c)) (-τ / ρ ^ 2) p) = p := by
  apply Prod.ext
  · simp only [affineParabolicPoint, smul_add, smul_neg, smul_smul,
      mul_inv_cancel₀ hρ, one_smul]
    abel
  · dsimp only [affineParabolicPoint]
    field_simp
    ring

theorem holderBound_affine_recovery {Q Q' : Set (Point n)} {β C ρ : ℝ}
    {c : Space n} {τ : ℝ} {f : Point n → E} (hρ : ρ ≠ 0)
    (hMap : MapsTo (affineParabolicPoint ρ⁻¹ (-(ρ⁻¹ • c)) (-τ / ρ ^ 2)) Q Q')
    (hf : HolderBound β Q' (fun p => f (affineParabolicPoint ρ c τ p)) C) :
    HolderBound β Q f ((1 + affineHolderScale ρ⁻¹ β) * C) := by
  apply holderBound_congr_on_native (holderBound_affine_general hMap hf)
  intro p hp
  dsimp only
  rw [affineParabolicPoint_inverse_right hρ]

end Yau.NodeProofs.F01Aux
