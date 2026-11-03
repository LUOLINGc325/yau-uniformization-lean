import Yau.LeafProofs.L05AutonomousHarnackMean

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The homogeneous estimate holds at every point of the actual closed scaled quarter cylinder. -/
theorem auto_weak_harnack_scaled_closed_quarter {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧
      ∀ (c : Space n) (R T : ℝ), 0 < R → ∀ v : Point n → ℝ,
        ContinuousOn v (autoClosed c R T) →
        (∀ z ∈ autoClosed c R T, 0 ≤ v z) →
        viscositySuper (autoOpen c R T) (fun H _ => -pucciPlus ell L (-H))
          (fun _ => 0) v →
        ∀ z ∈ autoClosed c (R/4) T, autoLpMean (autoEarly c R T) p v ≤ C*v z := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := auto_weak_harnack_closed_top hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_⟩
  intro c R T hR v hv hv0 hSuper z hz
  let u : Point n → ℝ := fun y => v (autoScale c R T y)
  have hu : ContinuousOn u (unitClosed n) := hv.comp
    (harnack_affine_contDiff c R (T-R^2) (R^2)).continuous.continuousOn
    (autoScale_closed_maps c hR T)
  have hu0 : ∀ y ∈ unitClosed n, 0 ≤ u y :=
    fun y hy => hv0 _ (autoScale_closed_maps c hR T hy)
  have hs := harnack_super_affine_pullback hell.le hL hSuper c hR
    (sq_pos_of_pos hR) (h := 1) zero_lt_one (autoScale_open_maps c hR T)
  have huSuper : viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H))
      (fun _ => 0) u := by
    simpa only [u, autoScale, harnackPucciMinus, div_self (sq_pos_of_pos hR).ne',
      one_mul, div_one, mul_zero] using hs
  rw [← autoScale_quarter_image c hR T] at hz
  obtain ⟨z',hz',rfl⟩ := hz
  have hh := hWH u hu hu0 huSuper z' (auto_quarter_closed_subset_late_closure n hz')
  change autoLpMean (harnackQminus n) p (fun y => v (autoScale c R T y)) ≤
    C*v (autoScale c R T z') at hh
  rwa [autoLpMean_scale_early c hR T p v] at hh

end Yau.LeafProofs.L05AutonomousAux
