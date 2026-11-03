import Yau.LeafProofs.L05AutonomousDeficitHarnackQuarter
import Yau.LeafProofs.L05AutonomousDeficitHarnackDyadic

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- One fixed exponent and constant handle the actual second limits and the continuous field. -/
theorem auto_limiting_deficit_harnack_shared {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧
      (∀ (c : Space n) (R T : ℝ), 0 < R → ∀ u w : Point n → ℝ,
        ∀ (e : Space n) (M B h0 : ℝ), Continuous u → Measurable w → 0 ≤ B → 0 < h0 →
        (∀ h, h ≠ 0 → |h| < h0 → ∀ z ∈ autoClosed c (R/2) T,
          |autoSecond u e h z| ≤ B ∧ autoSecond u e h z ≤ M) →
        (∀ h, h ≠ 0 → |h| < h0 →
          viscositySub (autoOpen c (R/2) T) (fun H _ => pucciPlus ell L H)
            (fun _ => 0) (autoSecond u e h)) →
        (∀ᵐ z ∂(volume : Measure (Point n)).restrict (autoEarly c (R/2) T),
          Tendsto (fun h : ℝ => autoSecond u e h z) (𝓝[>] 0) (𝓝 (w z))) →
        ∀ z ∈ autoClosed c (R/8) T,
          Tendsto (fun h : ℝ => autoSecond u e h z) (𝓝[>] 0) (𝓝 (w z)) →
          autoLpMean (autoEarly c (R/2) T) p (fun y => M-w y) ≤ C*(M-w z)) ∧
      (∀ (c : Space n) (R T : ℝ), 0 < R → ∀ (w : Point n → ℝ) (M : ℝ),
        ContinuousOn w (autoClosed c (R/2) T) →
        (∀ z ∈ autoClosed c (R/2) T, w z ≤ M) →
        viscositySub (autoOpen c (R/2) T) (fun H _ => pucciPlus ell L H)
          (fun _ => 0) w →
        ∀ z ∈ autoClosed c (R/8) T,
          autoLpMean (autoEarly c (R/2) T) p (fun y => M-w y) ≤ C*(M-w z)) := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := auto_weak_harnack_scaled_closed_quarter hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_,?_⟩
  · intro c R T hR u w e M B h0 hu hw hB hh0 hb hSub hlim z hz hzlim
    have hr : 0 < R/2 := div_pos hR (by norm_num)
    have hMean := auto_second_deficit_dyadic_mean_tendsto c hr hp hB hh0 u w e hu hw hb hlim
    have hValue : Tendsto (fun j => C*(M-autoSecond u e (autoDeficitDyadic h0 j) z))
        atTop (𝓝 (C*(M-w z))) :=
      (tendsto_const_nhds.sub (hzlim.comp (autoDeficitDyadic_tendsto_right hh0))).const_mul C
    apply le_of_tendsto_of_tendsto hMean hValue
    apply Eventually.of_forall
    intro j
    have hj0 := (autoDeficitDyadic_pos hh0 j).ne'
    have hjSmall := autoDeficitDyadic_abs_lt hh0 j
    have hCont : ContinuousOn (fun y => M-autoSecond u e (autoDeficitDyadic h0 j) y)
        (autoClosed c (R/2) T) :=
      (continuous_const.sub (autoSecond_continuous hu e _)).continuousOn
    have hNonneg : ∀ y ∈ autoClosed c (R/2) T,
        0 ≤ M-autoSecond u e (autoDeficitDyadic h0 j) y :=
      fun y hy => sub_nonneg.mpr (hb _ hj0 hjSmall y hy).2
    have hLate : z ∈ autoClosed c ((R/2)/4) T := by
      simpa only [show (R/2)/4 = R/8 by ring] using hz
    exact hWH c (R/2) T hr _ hCont hNonneg
      (auto_pucci_deficit_super (hSub _ hj0 hjSmall) M) z hLate
  · intro c R T hR w M hw hb hSub z hz
    have hLate : z ∈ autoClosed c ((R/2)/4) T := by
      simpa only [show (R/2)/4 = R/8 by ring] using hz
    exact hWH c (R/2) T (div_pos hR (by norm_num)) _
      (continuousOn_const.sub hw) (fun y hy => sub_nonneg.mpr (hb y hy))
      (auto_pucci_deficit_super hSub M) z hLate

/-- The positive all-step directional limits supplied by the actual Peano provider suffice. -/
theorem auto_second_limiting_deficit_harnack {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧
      ∀ (c : Space n) (R T : ℝ), 0 < R → ∀ u w : Point n → ℝ,
        ∀ (e : Space n) (M B h0 : ℝ), Continuous u → Measurable w → 0 ≤ B → 0 < h0 →
        (∀ h, h ≠ 0 → |h| < h0 → ∀ z ∈ autoClosed c (R/2) T,
          |autoSecond u e h z| ≤ B ∧ autoSecond u e h z ≤ M) →
        (∀ h, h ≠ 0 → |h| < h0 →
          viscositySub (autoOpen c (R/2) T) (fun H _ => pucciPlus ell L H)
            (fun _ => 0) (autoSecond u e h)) →
        (∀ᵐ z ∂(volume : Measure (Point n)).restrict (autoEarly c (R/2) T),
          Tendsto (fun h : ℝ => autoSecond u e h z) (𝓝[>] 0) (𝓝 (w z))) →
        ∀ z ∈ autoClosed c (R/8) T,
          Tendsto (fun h : ℝ => autoSecond u e h z) (𝓝[>] 0) (𝓝 (w z)) →
          autoLpMean (autoEarly c (R/2) T) p (fun y => M-w y) ≤ C*(M-w z) := by
  obtain ⟨p,C,hp,hp1,hC,hSecond,hContinuous⟩ := auto_limiting_deficit_harnack_shared hn hell hL
  exact ⟨p,C,hp,hp1,hC,hSecond⟩

/-- The original punctured-all-step formulation follows by restricting to positive steps. -/
theorem auto_second_limiting_deficit_harnack_punctured {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧
      ∀ (c : Space n) (R T : ℝ), 0 < R → ∀ u w : Point n → ℝ,
        ∀ (e : Space n) (M B h0 : ℝ), Continuous u → Measurable w → 0 ≤ B → 0 < h0 →
        (∀ h, h ≠ 0 → |h| < h0 → ∀ z ∈ autoClosed c (R/2) T,
          |autoSecond u e h z| ≤ B ∧ autoSecond u e h z ≤ M) →
        (∀ h, h ≠ 0 → |h| < h0 →
          viscositySub (autoOpen c (R/2) T) (fun H _ => pucciPlus ell L H)
            (fun _ => 0) (autoSecond u e h)) →
        (∀ᵐ z ∂(volume : Measure (Point n)).restrict (autoEarly c (R/2) T),
          Tendsto (fun h : ℝ => autoSecond u e h z) (𝓝[≠] 0) (𝓝 (w z))) →
        ∀ z ∈ autoClosed c (R/8) T,
          Tendsto (fun h : ℝ => autoSecond u e h z) (𝓝[≠] 0) (𝓝 (w z)) →
          autoLpMean (autoEarly c (R/2) T) p (fun y => M-w y) ≤ C*(M-w z) := by
  obtain ⟨p,C,hp,hp1,hC,hSecond⟩ := auto_second_limiting_deficit_harnack hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_⟩
  intro c R T hR u w e M B h0 hu hw hB hh0 hb hSub hlim z hz hzlim
  have hFilters : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] 0 :=
    nhdsWithin_mono 0 (fun x hx => by
      simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt hx))
  exact hSecond c R T hR u w e M B h0 hu hw hB hh0 hb hSub
    (hlim.mono (fun y hy => hy.mono_left hFilters)) z hz (hzlim.mono_left hFilters)

end Yau.LeafProofs.L05AutonomousAux
