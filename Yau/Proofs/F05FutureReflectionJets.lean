import Yau.Proofs.F05FutureReflection

/-! Exact computed jets on the reflected time segment. The time jet has
its actual affine slopes; no derivative of the original time jet occurs. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_future_tail_jets {X : Set (Space n)} {τ T : ℝ}
    (hτT : τ < T) (hBack : 0 ≤ 3*τ-2*T) {u : Point n → ℝ}
    (hu : C2 (cylinder X 0 τ) u) :
    C2 (cylinder X τ T) (F05FutureTail τ u) ∧
      ∀ p ∈ cylinder X τ T,
        spatialD (F05FutureTail τ u) p =
          (3 : ℝ) • F05TimeAffine (-1) (2*τ) (spatialD u) p-(2 : ℝ) • F05TimeAffine (-2) (3*τ) (spatialD u) p ∧
        spatialDD (F05FutureTail τ u) p =
          (3 : ℝ) • F05TimeAffine (-1) (2*τ) (spatialDD u) p-(2 : ℝ) • F05TimeAffine (-2) (3*τ) (spatialDD u) p ∧
        timeD (cylinder X τ T) (F05FutureTail τ u) p =
          3*((-1)*F05TimeAffine (-1) (2*τ) (timeD (cylinder X 0 τ) u) p)-
            2*((-2)*F05TimeAffine (-2) (3*τ) (timeD (cylinder X 0 τ) u) p) := by
  obtain ⟨hMap1,hMap2⟩ := F05_future_reflection_time_maps hτT.le hBack
  have hC1 := F05_c2_timeAffine hτT hMap1 hu
  have hC2 := F05_c2_timeAffine hτT hMap2 hu
  have hM1 : C2 (cylinder X τ T) (fun p => 3*F05TimeAffine (-1) (2*τ) u p) :=
    c2_spatial_mul (φ := fun _ => (3 : ℝ)) contDiff_const hC1
  have hM2 : C2 (cylinder X τ T) (fun p => 2*F05TimeAffine (-2) (3*τ) u p) :=
    c2_spatial_mul (φ := fun _ => (2 : ℝ)) contDiff_const hC2
  refine ⟨c2_sub hM1 hM2,?_⟩
  intro p hp
  refine ⟨?_,?_,?_⟩
  · change spatialD (fun p => 3*F05TimeAffine (-1) (2*τ) u p-2*F05TimeAffine (-2) (3*τ) u p) p = _
    rw [spatialD_sub hM1 hM2 hp,
      (F05_spatial_const_mul_jets 3 (F05TimeAffine (-1) (2*τ) u) p).1,
      (F05_spatial_const_mul_jets 2 (F05TimeAffine (-2) (3*τ) u) p).1]
    rfl
  · change spatialDD (fun p => 3*F05TimeAffine (-1) (2*τ) u p-2*F05TimeAffine (-2) (3*τ) u p) p = _
    rw [spatialDD_sub hM1 hM2 hp,
      (F05_spatial_const_mul_jets 3 (F05TimeAffine (-1) (2*τ) u) p).2,
      (F05_spatial_const_mul_jets 2 (F05TimeAffine (-2) (3*τ) u) p).2]
    rfl
  · change timeD _ (fun p => 3*F05TimeAffine (-1) (2*τ) u p-2*F05TimeAffine (-2) (3*τ) u p) p = _
    rw [timeD_sub hM1 hM2 hp,timeD_spatial_mul _ (fun _ => 3),timeD_spatial_mul _ (fun _ => 2),
      F05_timeD_timeAffine hτT hMap1 hu hp,F05_timeD_timeAffine hτT hMap2 hu hp]
    rfl

end Yau.Proofs.F05Aux
