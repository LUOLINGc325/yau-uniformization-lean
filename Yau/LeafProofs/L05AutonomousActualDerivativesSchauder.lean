import Yau.LeafProofs.L05AutonomousActualDerivativesTime

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

section Data
variable {n : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) {u V : Point n → ℝ}
  {G : Point n → Space n →L[ℝ] ℝ} {B : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
  (hu : ContinuousOn u (autoDerivativeClosed R)) (hG : ContinuousOn G (autoDerivativeClosed R))
  (hB : ContinuousOn B (autoDerivativeClosed R)) (hV : ContinuousOn V (autoDerivativeClosed R))
  (hScalarFTC : ∀ t∈Icc (-(R^2)) 0, ∀ x∈ball (0 : Space n) R, ∀ h : Space n,
    (∀ s∈Icc (0 : ℝ) 1, x+s • h∈ball 0 R) →
    u (x+h,t)-u (x,t)=∫ s in (0 : ℝ)..1, G (x+s • h,t) h)
  (hGradientFTC : ∀ t∈Icc (-(R^2)) 0, ∀ x∈ball (0 : Space n) R, ∀ h : Space n,
    (∀ s∈Icc (0 : ℝ) 1, x+s • h∈ball 0 R) →
    G (x+h,t)-G (x,t)=∫ s in (0 : ℝ)..1, B (x+s • h,t) h)
  (hTimeFTC : ∀ x∈ball (0 : Space n) R, ∀ a∈Icc (-(R^2)) 0, ∀ b∈Icc (-(R^2)) 0,
    u (x,b)-u (x,a)=∫ t in a..b, V (x,t))
include hr hrR hu hG hB hV hScalarFTC hGradientFTC hTimeFTC

theorem auto_C2_from_buffered_ftc : C2 (backward r) u := by
  have hSub := auto_backward_subset_derivativeClosed (n := n) hr hrR
  have hSpatial {p : Point n} (hp : p∈backward r) :=
    auto_spatial_from_buffered_ftc_on_backward hG hB hScalarFTC hGradientFTC hr hrR hp
  have hD : EqOn (spatialD u) G (backward r) := fun p hp => (hSpatial hp).2.2.1
  have hDD : EqOn (spatialDD u) B (backward r) := fun p hp => (hSpatial hp).2.2.2.1
  have hT : EqOn (timeD (backward r) u) V (backward r) :=
    fun p hp => auto_timeD_from_buffered_ftc hr hrR hV hTimeFTC hp
  refine ⟨hu.mono hSub,(hG.mono hSub).congr hD,(hB.mono hSub).congr hDD,
    (hV.mono hSub).congr hT,?_,?_⟩
  · exact fun p hp => (hSpatial hp).2.2.2.2
  · exact fun p hp => (auto_time_from_buffered_ftc hr hrR hV hTimeFTC hp).differentiableWithinAt

end Data

theorem auto_schauder_from_buffered_ftc {n : ℕ} {r R eta M0 M1 M2 Mt : ℝ}
    (hr : 0 < r) (hrR : r < R) (_heta : 0 < eta) (_heta1 : eta < 1)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hMt : 0 ≤ Mt) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point n → ℝ)
      (G : Point n → Space n →L[ℝ] ℝ) (B : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ) (V : Point n → ℝ),
      ContinuousOn u (autoDerivativeClosed R) → ContinuousOn G (autoDerivativeClosed R) →
      ContinuousOn B (autoDerivativeClosed R) → ContinuousOn V (autoDerivativeClosed R) →
      (∀ t∈Icc (-(R^2)) 0, ∀ x∈ball (0 : Space n) R, ∀ h : Space n,
        (∀ s∈Icc (0 : ℝ) 1, x+s • h∈ball 0 R) →
        u (x+h,t)-u (x,t)=∫ s in (0 : ℝ)..1, G (x+s • h,t) h) →
      (∀ t∈Icc (-(R^2)) 0, ∀ x∈ball (0 : Space n) R, ∀ h : Space n,
        (∀ s∈Icc (0 : ℝ) 1, x+s • h∈ball 0 R) →
        G (x+h,t)-G (x,t)=∫ s in (0 : ℝ)..1, B (x+s • h,t) h) →
      (∀ x∈ball (0 : Space n) R, ∀ a∈Icc (-(R^2)) 0, ∀ b∈Icc (-(R^2)) 0,
        u (x,b)-u (x,a)=∫ t in a..b, V (x,t)) →
      (∀ p∈autoDerivativeClosed R, |u p| ≤ M0) →
      (∀ p∈autoDerivativeClosed R, ‖G p‖ ≤ M1) →
      HolderBound eta (autoDerivativeClosed R) B M2 → HolderBound eta (autoDerivativeClosed R) V Mt →
      SchauderBound eta (backward r) u C := by
  let C := 1+M0+M1+M2+Mt
  have hC : 0 < C := by dsimp only [C]; linarith
  have h0C : M0 ≤ C := by dsimp only [C]; linarith
  have h1C : M1 ≤ C := by dsimp only [C]; linarith
  have h2C : M2 ≤ C := by dsimp only [C]; linarith
  have htC : Mt ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro u G B V hu hG hB hV hScalarFTC hGradientFTC hTimeFTC hU hGrad hBH hVH
  have hSub := auto_backward_subset_derivativeClosed (n := n) hr hrR
  have hSpatial {p : Point n} (hp : p∈backward r) :=
    auto_spatial_from_buffered_ftc_on_backward hG hB hScalarFTC hGradientFTC hr hrR hp
  have hD : EqOn (spatialD u) G (backward r) := fun p hp => (hSpatial hp).2.2.1
  have hDD : EqOn (spatialDD u) B (backward r) := fun p hp => (hSpatial hp).2.2.2.1
  have hT : EqOn (timeD (backward r) u) V (backward r) :=
    fun p hp => auto_timeD_from_buffered_ftc hr hrR hV hTimeFTC hp
  have hWeight (p q : Point n) : 0 ≤ holderWeight eta p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  refine ⟨auto_C2_from_buffered_ftc hr hrR hu hG hB hV hScalarFTC hGradientFTC hTimeFTC,hC.le,?_,?_,?_⟩
  · intro p hp
    refine ⟨(hU p (hSub hp)).trans h0C,?_⟩
    rw [hD hp]
    exact (hGrad p (hSub hp)).trans h1C
  · refine ⟨hC.le,?_,?_⟩
    · intro p hp
      rw [hDD hp]
      exact (hBH.2.1 p (hSub hp)).trans h2C
    · intro p hp q hq
      rw [hDD hp,hDD hq]
      exact (hBH.2.2 p (hSub hp) q (hSub hq)).trans (mul_le_mul_of_nonneg_right h2C (hWeight p q))
  · refine ⟨hC.le,?_,?_⟩
    · intro p hp
      rw [hT hp]
      exact (hVH.2.1 p (hSub hp)).trans htC
    · intro p hp q hq
      rw [hT hp,hT hq]
      exact (hVH.2.2 p (hSub hp) q (hSub hq)).trans (mul_le_mul_of_nonneg_right htC (hWeight p q))

end Yau.LeafProofs.L05AutonomousAux
