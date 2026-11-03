import Yau.LeafProofs.L19HeatMarkovPositivity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarHeat_setIntegral_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : Integrable f μ)
    (s : Set M.Carrier) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    (∫ x in s, scalarHeatFamily g μ hμ t f x ∂μ) ≤ ∫ x, f x ∂μ := by
  let χ : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs (1 : ℝ)
  have hχ : ∀ᵐ x ∂μ, 0 ≤ χ x ∧ χ x ≤ 1 := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
    change 0 ≤ (indicatorConstLp 2 hs hμs (1 : ℝ)) x ∧ _
    rw [hx]
    by_cases hxs : x ∈ s <;> simp [hxs]
  have hPχ := scalarHeatFamily_submarkov g μ hμ ht 1 zero_le_one χ hχ
  have hbounded : ∀ᵐ x ∂μ, ‖scalarHeatFamily g μ hμ t χ x‖ ≤ 1 :=
    hPχ.mono (fun x hx => by rw [Real.norm_of_nonneg hx.1]; exact hx.2)
  have hi := hf1.bdd_mul (Lp.memLp (scalarHeatFamily g μ hμ t χ)).aestronglyMeasurable hbounded
  calc
    _ = inner ℝ χ (scalarHeatFamily g μ hμ t f) :=
      (L2.inner_indicatorConstLp_one hs hμs (scalarHeatFamily g μ hμ t f)).symm
    _ = inner ℝ (scalarHeatFamily g μ hμ t χ) f := by
      rw [← ContinuousLinearMap.adjoint_inner_left, scalarHeatFamily_adjoint]
    _ = ∫ x, scalarHeatFamily g μ hμ t χ x * f x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    _ ≤ _ := integral_mono_ae hi hf1 (by
      filter_upwards [hf, hPχ] with x hfx hpx
      exact (mul_le_mul_of_nonneg_right hpx.2 hfx).trans_eq (one_mul _))

/-- Self-adjointness and the proved scalar Markov property imply the true
global L¹ contraction; no mass identity or maximum principle is assumed. -/
theorem scalarHeat_l1_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : Integrable f μ) :
    Integrable (scalarHeatFamily g μ hμ t f) μ ∧
      (∫ x, scalarHeatFamily g μ hμ t f x ∂μ) ≤ ∫ x, f x ∂μ := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  letI : SigmaFinite μ := inferInstance
  have hcover : AECover μ atTop (spanningSets μ) :=
    ⟨Filter.Eventually.of_forall (eventually_mem_spanningSets μ), measurableSet_spanningSets μ⟩
  have hbound (j : ℕ) : (∫ x in spanningSets μ j, scalarHeatFamily g μ hμ t f x ∂μ) ≤
      ∫ x, f x ∂μ := scalarHeat_setIntegral_le g μ hμ t ht f hf hf1 _
        (measurableSet_spanningSets μ j) (measure_spanningSets_lt_top μ j).ne
  have hpos := scalarHeatFamily_nonneg g μ hμ ht f hf
  have hi : Integrable (scalarHeatFamily g μ hμ t f) μ :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae (∫ x, f x ∂μ)
      (fun j => integrableOn_Lp_of_measure_ne_top (scalarHeatFamily g μ hμ t f)
        (by norm_num) (measure_spanningSets_lt_top μ j).ne)
      hpos (Filter.Eventually.of_forall hbound)
  exact ⟨hi, le_of_tendsto (hcover.integral_tendsto_of_countably_generated hi)
    (Filter.Eventually.of_forall hbound)⟩

end Yau.NodeProofs.P06Aux.TraceHilbert
