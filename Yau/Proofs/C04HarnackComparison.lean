import Yau.Proofs.C04CompactContraction

/-! The integrated Harnack factors tend uniformly to one on fixed compact sets. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem compact_scalar_harnack_comparison (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (K : Set (Pt X)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t, T ≤ t → ∀ x ∈ K,
      scalarCurvature (h t) x ≤ (1 + ε) * scalarCurvature (h (t + 1)) o ∧
      scalarCurvature (h t) o ≤ (1 + ε) * scalarCurvature (h (t + 1)) x := by
  obtain ⟨C, a, D, hC, ha, hD, hdist⟩ := compact_distance_power_bound X o h U P ρ hf hH K hK
  obtain ⟨H, hHarnack⟩ := hH.2.2.2.2.2.2.2.1
  let B := fun t : ℝ => Real.sqrt (C * t ^ (-a)) * D
  let F := fun t : ℝ => (1 + t⁻¹) * Real.exp (|H| * (B t) ^ 2)
  have hBlim : Tendsto B atTop (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ => C * t ^ (-a)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop ha).const_mul C
    simpa [B] using hp.sqrt.mul_const D
  have hFlim : Tendsto F atTop (𝓝 1) := by
    have hi : Tendsto (fun t : ℝ => 1 + t⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero
    have he : Tendsto (fun t => Real.exp (|H| * (B t) ^ 2)) atTop (𝓝 1) := by
      have hz : Tendsto (fun t => |H| * (B t) ^ 2) atTop (𝓝 0) := by
        simpa using (hBlim.pow 2).const_mul |H|
      simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hz
    simpa [F] using hi.mul he
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1
    ((tendsto_order.1 hFlim).2 (1 + ε) (by linarith))
  refine ⟨max 1 T₀, le_max_left _ _, ?_⟩
  intro t ht x hx
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have htplus : 0 ≤ t + 1 := by linarith
  have hBb : 0 ≤ B t := mul_nonneg (Real.sqrt_nonneg _) hD.le
  have hdb : distFrom (h t) o x ≤ B t := hdist t ht1 x hx
  have hd0 : 0 ≤ distFrom (h t) o x :=
    LeafProofs.L23Aux.inducedDistance_nonneg (h t)
      (localizedFlow_metricSmooth X o h U P ρ hf htpos.le) o x
  have hsq : (distFrom (h t) o x) ^ 2 ≤ (B t) ^ 2 := (sq_le_sq₀ hd0 hBb).mpr hdb
  have hexp : H * (distFrom (h t) o x) ^ 2 ≤ |H| * (B t) ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self H) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg H))
  have hfrac : (t + 1) / t = 1 + t⁻¹ := by field_simp
  have hfactor : (t + 1) / t * Real.exp (H * distFrom (h t) o x ^ 2) ≤ 1 + ε := by
    calc
      (t + 1) / t * Real.exp (H * distFrom (h t) o x ^ 2) ≤
          (1 + t⁻¹) * Real.exp (|H| * (B t) ^ 2) := by
        rw [hfrac]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ ≤ 1 + ε := (hT₀ t ((le_max_right _ _).trans ht)).le
  have hsym : distFrom (h t) x o = distFrom (h t) o x :=
    LeafProofs.L23Aux.inducedDistance_symm (h t)
      (localizedFlow_metricSmooth X o h U P ρ hf htpos.le) x o
  constructor
  · have hw := hHarnack x o t (t + 1) htpos (by linarith)
    simp only [show t + 1 - t = 1 by ring, div_one, hsym] at hw
    have hm := mul_le_mul_of_nonneg_left hfactor (scalar_pos X o h hH htplus o).le
    calc
      scalarCurvature (h t) x ≤
          scalarCurvature (h (t + 1)) o * ((t + 1) / t) *
            Real.exp (H * distFrom (h t) o x ^ 2) := hw
      _ ≤ (1 + ε) * scalarCurvature (h (t + 1)) o := by nlinarith
  · have hw := hHarnack o x t (t + 1) htpos (by linarith)
    simp only [show t + 1 - t = 1 by ring, div_one] at hw
    have hm := mul_le_mul_of_nonneg_left hfactor (scalar_pos X o h hH htplus x).le
    calc
      scalarCurvature (h t) o ≤
          scalarCurvature (h (t + 1)) x * ((t + 1) / t) *
            Real.exp (H * distFrom (h t) o x ^ 2) := hw
      _ ≤ (1 + ε) * scalarCurvature (h (t + 1)) x := by nlinarith

end Yau.Proofs.C04Aux
