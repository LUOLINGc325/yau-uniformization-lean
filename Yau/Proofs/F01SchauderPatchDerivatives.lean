import Yau.Proofs.F01SchauderScalarMultiplication
import Yau.Proofs.F01ClosedBackwardRestriction

/-! Recover the actual Hessian and one-sided time derivative from a
rescaled Schauder estimate. The inverse square scale is explicit and
the lower-open backward face agrees with the closed-cylinder derivative. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem affine_schauder_patch_hessian_holder {κ β C τ : ℝ} {c : Space n}
    {u : Point n → ℝ} (hκ : κ ≠ 0)
    (hSch : SchauderBound β (backward 1) (affineParabolicPullback κ c τ u) C) :
    HolderBound β (backward 1) (fun p => spatialDD u (affineParabolicPoint κ c τ p))
      (|(κ ^ 2)⁻¹| * C) := by
  apply holderBound_congr_on_native
    (holderBound_real_smul_native hSch.2.2.2.1 ((κ ^ 2)⁻¹))
  intro p hp
  dsimp only
  rw [spatialDD_affineParabolicPullback, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 hκ), one_smul]

theorem affine_schauder_patch_time_holder {κ β C τ l r : ℝ} {c : Space n}
    {S : Set (Space n)} {u : Point n → ℝ} (hκ : κ ≠ 0)
    (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => κ • x + c) (ball 0 1) S)
    (hClock : MapsTo (fun t => τ + κ ^ 2 * t) (Icc (-1) 0) (Icc l r))
    (hSch : SchauderBound β (backward 1) (affineParabolicPullback κ c τ u) C) :
    HolderBound β (backward 1) (fun p => timeD (cylinder S l r) u (affineParabolicPoint κ c τ p))
      (|(κ ^ 2)⁻¹| * C) := by
  apply holderBound_congr_on_native
    (holderBound_real_smul_native hSch.2.2.2.2 ((κ ^ 2)⁻¹))
  intro p hp
  have hc : p ∈ cylinder (ball 0 1) (-1) 0 :=
    ⟨hp.1, by simpa only [one_pow] using hp.2.1.le, hp.2.2⟩
  have hd := timeD_affineParabolicPullback (by norm_num : (-1 : ℝ) < 0)
    hu hSpace hClock hc
  have hb := timeD_closed_open_lower (affineParabolicPullback κ c τ u) hp
  simp only [one_pow] at hb
  have ht : timeD (backward 1) (affineParabolicPullback κ c τ u) p =
      κ ^ 2 * timeD (cylinder S l r) u (affineParabolicPoint κ c τ p) := by
    simpa only [backward, one_pow] using hb.symm.trans hd
  dsimp only
  rw [ht]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hκ), one_mul]

end Yau.NodeProofs.F01Aux
