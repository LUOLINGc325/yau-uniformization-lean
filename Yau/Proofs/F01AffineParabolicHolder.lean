import Yau.Proofs.F01AffineParabolicSpatialJets

/-! Every small affine parabolic chart map contracts the actual Holder
weight. Thus it transports the original numerical Holder predicate with
the same constant, before any field realization. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem holderWeight_affineParabolicPoint_le {ρ β : ℝ} (hρ : |ρ| ≤ 1) (hβ : 0 ≤ β)
    (c : Space n) (τ : ℝ) (p q : Point n) :
    holderWeight β (affineParabolicPoint ρ c τ p) (affineParabolicPoint ρ c τ q) ≤
      holderWeight β p q := by
  have hSpace : ‖(affineParabolicPoint ρ c τ p).1 - (affineParabolicPoint ρ c τ q).1‖ ≤
      ‖p.1 - q.1‖ := by
    have he : ρ • p.1 + c - (ρ • q.1 + c) = ρ • (p.1 - q.1) := by rw [smul_sub]; abel
    change ‖ρ • p.1 + c - (ρ • q.1 + c)‖ ≤ _
    rw [he, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hρ (norm_nonneg _)).trans_eq (one_mul _)
  have hTime : |(affineParabolicPoint ρ c τ p).2 - (affineParabolicPoint ρ c τ q).2| ≤
      |p.2 - q.2| := by
    have he : τ + ρ ^ 2 * p.2 - (τ + ρ ^ 2 * q.2) = ρ ^ 2 * (p.2 - q.2) := by ring
    change |τ + ρ ^ 2 * p.2 - (τ + ρ ^ 2 * q.2)| ≤ _
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) ((sq_le_one_iff_abs_le_one ρ).mpr hρ)
  unfold holderWeight
  exact add_le_add (Real.rpow_le_rpow (norm_nonneg _) hSpace hβ)
    (Real.rpow_le_rpow (abs_nonneg _) hTime (div_nonneg hβ (by norm_num)))

theorem holderBound_affineParabolicPullback {V : Type*} [NormedAddCommGroup V]
    {Q Q' : Set (Point n)} {β C ρ : ℝ} {c : Space n} {τ : ℝ} {f : Point n → V}
    (hρ : |ρ| ≤ 1) (hβ : 0 ≤ β)
    (hMap : MapsTo (affineParabolicPoint ρ c τ) Q' Q) (hf : HolderBound β Q f C) :
    HolderBound β Q' (fun p => f (affineParabolicPoint ρ c τ p)) C := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    exact hf.2.1 _ (hMap hp)
  · intro p hp q hq
    exact (hf.2.2 _ (hMap hp) _ (hMap hq)).trans
      (mul_le_mul_of_nonneg_left (holderWeight_affineParabolicPoint_le hρ hβ c τ p q) hf.1)

theorem holderBound_congr_on_native {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {β C : ℝ} {f g : Point n → V}
    (hf : HolderBound β Q f C) (he : EqOn f g Q) : HolderBound β Q g C := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    rw [← he hp]
    exact hf.2.1 p hp
  · intro p hp q hq
    rw [← he hp, ← he hq]
    exact hf.2.2 p hp q hq

end Yau.NodeProofs.F01Aux
