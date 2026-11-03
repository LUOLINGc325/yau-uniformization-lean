import Yau.Proofs.C05ScalarHarnackSecondTimeBound
import Yau.Proofs.C05TaylorSequenceLimits

/-! Actual temporal Taylor analysis on the original normalized sequence.
Only the original finite jet and clock windows enter the derivative bound;
finite initial indices are removed by an explicit constant extension. -/
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint Yau.Proofs.C05NormalizedScalarTimeEvolutionAux Yau.Proofs.C05TaylorSequenceAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem original_sequence_scalarHarnack_time_decay (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) {δ B K : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hdefect : Tendsto (fun i => scalarHarnackSum h o (tw i) /
      scalarCurvature (h (tw i)) o^2) atTop (𝓝 0))
    (hwindow : ∀ᶠ i in atTop, ∀ z : ℝ, |z| < δ →
      0 < tw i+z/scalarCurvature (h (tw i)) o ∧
      |(tw i*scalarCurvature (h (tw i)) o+z)⁻¹| ≤ K ∧
      (∀ j ≤ 6, scalarJetNorm (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
        (scalarCurvature (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)) j o ≤ B) ∧
      (∀ j ≤ 4, realRicciJetNorm (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z) j o ≤ B)) :
    Tendsto (fun i => deriv (fun z => scalarHarnackSource
      (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
      (tw i*scalarCurvature (h (tw i)) o+z)⁻¹ o) 0) atTop (𝓝 0) := by
  let F : ℕ → ℝ → ℝ := fun i z => scalarHarnackSource
    (normalizedMetric h (tw i) (scalarCurvature (h (tw i)) o) (hRi i) z)
    (tw i*scalarCurvature (h (tw i)) o+z)⁻¹ o
  obtain ⟨N,hN⟩ := eventually_atTop.1 hwindow
  let G : ℕ → ℝ → ℝ := fun i => if N ≤ i then F i else fun _ => 0
  let C := scalarHarnackSecondTimeBudget n B K
  have hC : 0 ≤ C := scalarHarnackSecondTimeBudget_nonneg n hB hK
  have hG (i : ℕ) : ContDiffOn ℝ 2 (G i) (Ioo (-δ) δ) := by
    by_cases hi : N ≤ i
    · simp only [G,if_pos hi]
      intro z hz
      have ht := (hN i hi z (abs_lt.mpr hz)).1
      exact ((normalized_scalarHarnack_contDiffAt o h U P ρ hf (tw i)
        (scalarCurvature (h (tw i)) o) (hRi i) o z ht).of_le (by simp)).contDiffWithinAt
    · simpa only [G,if_neg hi] using (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (0:ℝ))).contDiffOn
  have hnonneg (i : ℕ) (z : ℝ) (hz : z ∈ Ioo (-δ) δ) : 0 ≤ G i z := by
    by_cases hi : N ≤ i
    · simpa only [G,if_pos hi] using normalized_scalarHarnack_nonneg o h U P ρ hf hH
        (tw i) (scalarCurvature (h (tw i)) o) (hRi i) o z (hN i hi z (abs_lt.mpr hz)).1
    · simp only [G,if_neg hi,le_refl]
  have hbound (i : ℕ) (z : ℝ) (hz : z ∈ Ioo (-δ) δ) : |iteratedDeriv 2 (G i) z| ≤ C := by
    by_cases hi : N ≤ i
    · obtain ⟨ht,hclock,hS,hR⟩ := hN i hi z (abs_lt.mpr hz)
      simpa only [G,if_pos hi] using normalized_scalarHarnack_second_deriv_abs_le o h U P ρ hf
        (tw i) (scalarCurvature (h (tw i)) o) (hRi i) o z ht hB hK hclock hS hR
    · simp only [G,if_neg hi]
      have hc : deriv (fun _ : ℝ => (0:ℝ)) = fun _ => 0 := funext (fun t => deriv_const t 0)
      simp only [iteratedDeriv_succ,iteratedDeriv_zero,hc,deriv_const,abs_zero]
      exact hC
  have hzero : Tendsto (fun i => G i 0) atTop (𝓝 0) := by
    apply hdefect.congr'
    filter_upwards [eventually_ge_atTop N] with i hi
    simp only [G,if_pos hi]
    have he := normalizedScalarHarnackSum_eq_source o h U P ρ hf (tw i)
      (scalarCurvature (h (tw i)) o) (hRi i) o 0 (by simpa only [zero_div,add_zero] using htw i)
    simpa only [F,normalizedMetric,zero_div,add_zero] using he
  have hd := deriv_tendsto_zero G hδ hC hG hnonneg hbound hzero
  apply hd.congr'
  filter_upwards [eventually_ge_atTop N] with i hi
  simp only [G,if_pos hi,F]

end Yau.Proofs.C05Aux
