import Yau.Proofs.C04ClockInverse
import Yau.Proofs.C04ClockRescaling
import Yau.Proofs.C04RescaledTubeClockBarrier

/-! A single sequence tail and a single time radius control the rescaled
basepoint scalar curvature, before any spatial radius is chosen. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint C04Aux
variable {n : ℕ}

theorem rescaled_window_base_bounds (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (a K : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hK : 1 ≤ K) (S tw : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (hwindow : ∀ i t t', 0 ≤ t → 0 ≤ t' → ρ o t = 2 * S i →
      ρ o t' = a * S i → clockSpeed o h t ≤ K * clockSpeed o h t')
    (htw : ∀ i, 0 < tw i) (htwinf : Tendsto tw atTop atTop)
    (hmiddle : ∀ i, 5 * S i / 4 ≤ ρ o (tw i) ∧ ρ o (tw i) ≤ 7 * S i / 4) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∃ N : ℕ, ∀ i, N ≤ i →
      8 * δ ≤ clockSpeed o h (tw i) ∧
      ∀ hR : 0 < scalarCurvature (h (tw i)) o, ∀ z : ℝ, |z| ≤ δ →
        0 < tw i + z / scalarCurvature (h (tw i)) o ∧
        scalarCurvature (scaleField (scalarCurvature (h (tw i)) o) hR
          (h (tw i + z / scalarCurvature (h (tw i)) o))) o ≤ B := by
  obtain ⟨c, hc, hclower⟩ := clockSpeed_positive_lower X o h U P ρ hf hH
  obtain ⟨A, hA, hsA, time, htime, hinv, htimemono, htimeinf⟩ :=
    clock_inverse X o h U P ρ hf hH
  let δ := c / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have htail : ∀ᶠ i : ℕ in atTop,
      1 ≤ tw i ∧ 0 < S i ∧ ρ o A ≤ a * S i ∧ 8 * K * δ < S i := by
    filter_upwards [htwinf.eventually (eventually_ge_atTop 1),
      hS.eventually (eventually_gt_atTop 0),
      (hS.const_mul_atTop ha).eventually (eventually_ge_atTop (ρ o A)),
      hS.eventually (eventually_gt_atTop (8 * K * δ))] with i hi hsi hai hbig
    exact ⟨hi, hsi, hai, hbig⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  refine ⟨δ, 2 * K, hδ, by positivity, N, ?_⟩
  intro i hi
  obtain ⟨hti, hSi, haSi, hbig⟩ := hN i hi
  have hci0 := hclower (tw i) hti
  refine ⟨by dsimp only [δ]; linarith, ?_⟩
  intro hR z hz
  let ti := tw i
  let Ri := scalarCurvature (h ti) o
  have hRi : 0 < Ri := hR
  have hci : c ≤ ti * Ri := hclower ti hti
  have haSS : a * S i ≤ S i := by nlinarith
  have hSlevel : ρ o A ≤ S i := haSi.trans haSS
  have h2Slevel : ρ o A ≤ 2 * S i := by linarith
  obtain ⟨hTA, hsTA⟩ := htime (a * S i) haSi
  obtain ⟨hL, hsL⟩ := htime (S i) hSlevel
  obtain ⟨hHtime, hsH⟩ := htime (2 * S i) h2Slevel
  let L := time (S i)
  let H := time (2 * S i)
  have hL1 : 1 ≤ L := hA.trans hL
  have hH1 : 1 ≤ H := hA.trans hHtime
  have hTA1 : 1 ≤ time (a * S i) := hA.trans hTA
  have hsm := (rho_strictMonoOn_nonneg X o h U P ρ hf hH)
  have hLt : L ≤ ti := by
    by_contra hn
    have hh := hsm (htw i).le (zero_le_one.trans hL1) (lt_of_not_ge hn)
    have hm := (hmiddle i).1
    change ρ o ti < ρ o L at hh
    rw [hsL] at hh
    linarith
  have htH : ti ≤ H := by
    by_contra hn
    have hh := hsm (zero_le_one.trans hH1) (htw i).le (lt_of_not_ge hn)
    have hm := (hmiddle i).2
    change ρ o H < ρ o ti at hh
    rw [hsH] at hh
    linarith
  have hTAti : time (a * S i) ≤ ti := by
    have hm := htimemono.monotoneOn haSi hSlevel haSS
    exact hm.trans hLt
  have hqm := clockSpeed_monotoneOn X o h U P ρ hf hH zero_lt_one
  have hqH : clockSpeed o h H ≤ K * clockSpeed o h ti := by
    have hw := hwindow i H (time (a * S i))
      (zero_le_one.trans hH1) (zero_le_one.trans hTA1) hsH hsTA
    exact hw.trans (mul_le_mul_of_nonneg_left (hqm hTA1 hti hTAti) hKpos.le)
  have hdupper : ∀ u ∈ Set.Icc L H, ti / 2 ≤ u →
      scalarCurvature (h u) o ≤ (2 * K) * Ri := by
    intro u hu hut
    have hu1 : 1 ≤ u := hL1.trans hu.1
    have hup : 0 < u := zero_lt_one.trans_le hu1
    have hqu := (hqm hu1 hH1 hu.2).trans hqH
    change u * scalarCurvature (h u) o ≤ K * (ti * Ri) at hqu
    have htr : K * (ti * Ri) ≤ (2 * K * Ri) * u := by
      have hm := mul_le_mul_of_nonneg_left hut (mul_nonneg hKpos.le hRi.le)
      nlinarith
    exact (mul_le_mul_iff_right₀ hup).1 (hqu.trans (by nlinarith [htr]))
  have hhalf : δ / Ri < ti / 2 := by
    apply (div_lt_iff₀ hRi).2
    dsimp only [δ]
    nlinarith
  have hbar := clock_window_time_barrier hRi hδ (by positivity : 0 ≤ 2 * K)
    hhalf hLt htH (m := S i / 4)
    (by have hh := (hmiddle i).1; rw [hsL]; change 5 * S i / 4 ≤ ρ o ti at hh; linarith)
    (by have hh := (hmiddle i).2; rw [hsH]; change ρ o ti ≤ 7 * S i / 4 at hh; linarith)
    (by nlinarith)
    (fun u hu => rho_hasDerivAt X o h U P ρ hf o
      (zero_lt_one.trans_le (hL1.trans hu.1))) hdupper
  have hzu : -δ ≤ z ∧ z ≤ δ := abs_le.1 hz
  have hshift : ti - δ / Ri ≤ ti + z / Ri ∧ ti + z / Ri ≤ ti + δ / Ri := by
    constructor
    · have hh := div_le_div_of_nonneg_right hzu.1 hRi.le
      rw [neg_div] at hh
      linarith
    · have hh := div_le_div_of_nonneg_right hzu.2 hRi.le
      linarith
  have hmem : ti + z / Ri ∈ Set.Icc L H :=
    ⟨hbar.1.le.trans hshift.1, hshift.2.trans hbar.2.le⟩
  have hpositive : 0 < ti + z / Ri := zero_lt_one.trans_le (hL1.trans hmem.1)
  refine ⟨hpositive, ?_⟩
  rw [scalar_scaleField]
  have hh := hdupper _ hmem (by linarith [hshift.1])
  change Ri⁻¹ * scalarCurvature (h (ti + z / Ri)) o ≤ 2 * K
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ hRi).2 (by nlinarith [hh])

end Yau.Proofs.C04RescaledTubeAux
