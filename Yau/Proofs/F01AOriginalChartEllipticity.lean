import Yau.Proofs.F01ChartGramSmooth
import Yau.Proofs.F01MatrixSandwichMono
import Yau.Proofs.F01RelativeScalarSandwich

/-! The ellipticity constants come from a compact part of the original
chart and a local metric comparison. No global approximation-chart bound
is used, so the constants precede the approximation index. -/
noncomputable section
open Set
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem original_chart_compact_matrix_sandwich
    (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ z ∈ K,
      (pullbackMatrix g e z - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      ((D : ℂ) • 1 - pullbackMatrix g e z).PosSemidef := by
  have hG : ContinuousOn (fun z => pullbackMatrix g e z) K :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j =>
      (pullbackMatrix_entry_contDiffOn g hg e he i j).continuousOn.mono hKe))
  obtain ⟨D, hD, hb⟩ := compact_posDef_matrix_sandwich hK hG
    (fun z hz => pullbackMatrix_posDef g e he hei (hKe hz))
  exact ⟨max 1 D, le_max_left _ _, fun z hz =>
    matrix_sandwich_mono hD (by positivity) (le_max_right _ _) (hb z hz)⟩

theorem fixed_original_chart_uniform_ellipticity
    {ι : Type*} (G : Space n → Matrix (Fin n) (Fin n) ℂ)
    (H : ι → Point n → Matrix (Fin n) (Fin n) ℂ)
    {K : Set (Space n)} {Q : Set (Point n)} {D c C : ℝ}
    (hD : 1 ≤ D) (hc : 0 < c) (hcC : c ≤ C)
    (hQ : ∀ p ∈ Q, p.1 ∈ K)
    (hG : ∀ z ∈ K, (G z - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      ((D : ℂ) • 1 - G z).PosSemidef)
    (hH : ∀ i p, p ∈ Q →
      (H i p - (c : ℂ) • G p.1).PosSemidef ∧
      ((C : ℂ) • G p.1 - H i p).PosSemidef) :
    0 < c * D⁻¹ ∧ c * D⁻¹ ≤ C * D ∧ ∀ i p, p ∈ Q →
      (H i p - ((c * D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      (((C * D : ℝ) : ℂ) • 1 - H i p).PosSemidef := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hCp : 0 < C := hc.trans_le hcC
  refine ⟨mul_pos hc (inv_pos.mpr hDp), ?_, ?_⟩
  · calc
      c * D⁻¹ ≤ c * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hD) hc.le
      _ = c := mul_one c
      _ ≤ C := hcC
      _ ≤ C * D := le_mul_of_one_le_right hCp.le hD
  · intro i p hp
    exact relative_scalar_matrix_sandwich hc.le hCp.le
      (hG p.1 (hQ p hp)).1 (hG p.1 (hQ p hp)).2 (hH i p hp).1 (hH i p hp).2

end Yau.NodeProofs.F01Aux
