import Yau.Proofs.F01AffineParabolicC2
import Yau.Proofs.F01AffineParabolicHolder
import Yau.Proofs.F01NormalizedScalarSourceHolder

/-! A small affine parabolic chart change preserves the original
Schauder bound, with the actual Hessian and one-sided time derivatives.
No joint extension at a closed time face is required. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem schauderBound_affineParabolicPullback {S O : Set (Space n)}
    {l r a b ρ τ β C : ℝ} {c : Space n} {u : Point n → ℝ}
    (hab : a < b) (hρ : |ρ| ≤ 1) (hβ : 0 ≤ β)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    (hu : SchauderBound β (cylinder S l r) u C) :
    SchauderBound β (cylinder O a b) (affineParabolicPullback ρ c τ u) C := by
  have hMap : MapsTo (affineParabolicPoint ρ c τ) (cylinder O a b) (cylinder S l r) :=
    fun p hp => ⟨hSpace hp.1, hClock hp.2⟩
  have hSq : |ρ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one ρ).mpr hρ
  have hDD := holderBound_real_smul_of_abs_le_one
    (holderBound_affineParabolicPullback hρ hβ hMap hu.2.2.2.1) hSq
  have hTime := holderBound_real_smul_of_abs_le_one
    (holderBound_affineParabolicPullback hρ hβ hMap hu.2.2.2.2) hSq
  refine ⟨c2_affineParabolicPullback hab hu.1 hSpace hClock, hu.2.1, ?_, ?_, ?_⟩
  · intro p hp
    refine ⟨(hu.2.2.1 _ (hMap hp)).1, ?_⟩
    rw [spatialD_affineParabolicPullback, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hρ (hu.2.2.1 _ (hMap hp)).2 (norm_nonneg _) zero_le_one).trans_eq
      (one_mul C)
  · apply holderBound_congr_on_native hDD
    intro p hp
    exact (spatialDD_affineParabolicPullback ρ c τ u p).symm
  · apply holderBound_congr_on_native hTime
    intro p hp
    exact (timeD_affineParabolicPullback hab hu.1 hSpace hClock hp).symm

end Yau.NodeProofs.F01Aux
