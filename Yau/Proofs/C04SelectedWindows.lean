import Yau.Proofs.C04WindowSequence
import Yau.Proofs.C04MiddleSelection
import Yau.Proofs.C04Scaling

/-! Good windows with actual middle physical times and the vanishing logarithmic derivative. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem selected_window_sequence (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ S : ℕ → ℝ, ∃ K : ℝ, 1 ≤ K ∧ Tendsto S atTop atTop ∧
      (∀ i t t', 0 ≤ t → 0 ≤ t' → ρ o t = 2 * S i → ρ o t' = a * S i →
        clockSpeed o h t ≤ K * clockSpeed o h t') ∧
      ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
        (∀ i, 5 * S i / 4 ≤ ρ o (tw i) ∧ ρ o (tw i) ≤ 7 * S i / 4) ∧
        Tendsto (fun i => deriv (clockSpeed o h) (tw i) /
          (clockSpeed o h (tw i) * scalarCurvature (h (tw i)) o)) atTop (𝓝 0) ∧
        (∀ i, 0 < scalarCurvature (h (tw i)) o) ∧
        (∀ i (hR : 0 < scalarCurvature (h (tw i)) o),
          scalarCurvature (scaleField (scalarCurvature (h (tw i)) o) hR (h (tw i))) o = 1) := by
  obtain ⟨S, K, hSpos, hSinf, hwindow⟩ := good_window_sequence X o h U P ρ hf hH ha ha1
  obtain ⟨B, hB, hmiddle⟩ := middle_point_of_good_window X o h U P ρ hf hH ha ha1
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hSinf) B
  let S' := fun i : ℕ => S (i + N)
  let K' := max K 2
  have hK' : 1 ≤ K' := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_right _ _)
  have hshift : Tendsto (fun i : ℕ => i + N) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right i N) tendsto_id
  have hS'inf : Tendsto S' atTop atTop := hSinf.comp hshift
  have hwindow' : ∀ i t t', 0 ≤ t → 0 ≤ t' →
      ρ o t = 2 * S' i → ρ o t' = a * S' i →
      clockSpeed o h t ≤ K' * clockSpeed o h t' := by
    intro i t t' ht ht' hst hst'
    have hw := hwindow (i + N) t t' ht ht' hst hst'
    have hq : 0 ≤ clockSpeed o h t' := mul_nonneg ht'
      (scalar_pos X o h hH ht' o).le
    exact hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  choose tw htwpos hleft hright hnonneg hupper using
    fun i => hmiddle (S' i) K' (hN (i + N) (Nat.le_add_left N i)) hK' (hwindow' i)
  have htwinf : Tendsto tw atTop atTop := by
    apply tendsto_atTop_atTop.2
    intro T
    let T' := max T 0
    obtain ⟨J, hJ⟩ := (tendsto_atTop_atTop.1 hS'inf) ((4 / 5 : ℝ) * (ρ o T' + 1))
    refine ⟨J, ?_⟩
    intro i hi
    have hbig := hJ i hi
    have hT' : T' ≤ tw i := by
      by_contra hn
      have hsmall := (rho_strictMonoOn_nonneg X o h U P ρ hf hH).monotoneOn
        (htwpos i).le (le_max_right T 0) (le_of_lt (lt_of_not_ge hn))
      have hleft' := hleft i
      linarith
    exact (le_max_left T 0).trans hT'
  have hratioinf : Tendsto (fun i => deriv (clockSpeed o h) (tw i) /
      (clockSpeed o h (tw i) * scalarCurvature (h (tw i)) o)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hS'inf.const_div_atTop (2 * Real.log K')) hnonneg hupper
  exact ⟨S', K', hK', hS'inf, hwindow', tw, htwpos, htwinf,
    fun i => ⟨hleft i, hright i⟩, hratioinf,
    fun i => scalar_pos X o h hH (htwpos i).le o,
    fun i hR => scalar_normalized (h (tw i)) o hR⟩

end Yau.Proofs.C04Aux
