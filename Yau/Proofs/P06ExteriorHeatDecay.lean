import Yau.Proofs.P06ExteriorHeatSource
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexOrder Matrix

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.Blueprint Yau.LeafProofs L03 Davies
variable {n k : ℕ} {M : ComplexManifold n}

/-- The compact cutoff derivative has exactly the exterior support required
by the transposed all-degree Davies estimate. -/
theorem cutoffExteriorVector_outside (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hclosed : ClosedRealForm A)
    (j : ℕ) (hj : 1 ≤ j) :
    indicator g μ (distBall g.form o j)ᶜ (L12Aux.measurableSet_distBall g o j).compl
      (cutoffExteriorVector g μ hμ o χ hχ A hA j hj) =
        cutoffExteriorVector g μ hμ o χ hχ A hA j hj := by
  apply indicator_realize_eq_self
  exact Eventually.of_forall fun x hx => cutoff_exterior_zero_inside g o χ hχ A hA hclosed j hj x
    (by simpa only [Set.mem_compl_iff,not_not] using hx)

/-- One moving annulus gives local error decay; no derivative Gaussian is used. -/
theorem cutoffExteriorVector_local_heat_tendsto_zero
    (g : SmoothMetric M) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hclosed : ClosedRealForm A)
    (B0 : ℝ) (hb : ∀ x, formNormSq g.form A x ≤ B0^2)
    (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    Tendsto (fun j : ℕ => ‖indicator g μ (distBall g.form o r)
      (L12Aux.measurableSet_distBall g o r) (hodgeHeatHilbert g μ hμ (k+1) t
        (cutoffExteriorVector g μ hμ o χ hχ A hA (j+1) (by omega)))‖) atTop (𝓝 0) := by
  obtain ⟨a,ha,htail⟩ := exists_uniform_annular_heat_L2_tail n
  obtain ⟨K,hK0,hsource⟩ := cutoffExteriorVector_polynomial_bound g hK hRic μ hμ o χ hχ A hA hclosed B0 hb
  let β : ℝ := 1/(4*a^2*t)
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hden : 0 < a^2*t := mul_pos (sq_pos_of_pos hap) ht
  have hβ : 0 < β := by dsimp only [β]; positivity
  let F : ℕ → ℝ := fun j => ‖indicator g μ (distBall g.form o r)
    (L12Aux.measurableSet_distBall g o r) (hodgeHeatHilbert g μ hμ (k+1) t
      (cutoffExteriorVector g μ hμ o χ hχ A hA (j+1) (by omega)))‖
  have hxlim : Tendsto (fun j : ℕ => ((j+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdecay : Tendsto (fun j : ℕ => K * (((j+1:ℕ):ℝ)^(2*n) *
      Real.exp (-β*((j+1:ℕ):ℝ)))) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*n:ℕ):ℝ) β hβ).comp hxlim).const_mul K
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using hh
  have hbound : ∀ᶠ j : ℕ in atTop, (F j)^2 ≤ K * (((j+1:ℕ):ℝ)^(2*n) * Real.exp (-β*((j+1:ℕ):ℝ))) := by
    filter_upwards [hxlim.eventually (eventually_ge_atTop (max 1 (2*r)))] with j hj
    let x : ℝ := ((j+1:ℕ):ℝ)
    have hx1 : 1 ≤ x := (le_max_left 1 (2*r)).trans hj
    have hxr : 2*r ≤ x := (le_max_right 1 (2*r)).trans hj
    have hrx : r < x := by linarith
    have htailj := CutoffTail.reverse_annular_tail g μ hμ o a ha
      (htail M g μ hμ (k+1) o) r x t hr hrx ht
      (cutoffExteriorVector g μ hμ o χ hχ A hA (j+1) (by omega))
      (cutoffExteriorVector_outside g μ hμ o χ hχ A hA hclosed (j+1) (by omega))
    change F j ≤ _ at htailj
    have hs := pow_le_pow_left₀ (norm_nonneg _) htailj 2
    have hexp : (Real.exp (-(x-r)^2/(2*a^2*t)))^2 = Real.exp (-(x-r)^2/(a^2*t)) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [mul_pow,hexp] at hs
    have he : -(x-r)^2/(a^2*t) ≤ -β*x := by
      dsimp only [β]
      have hh : x ≤ 4*(x-r)^2 := by
        nlinarith [sq_nonneg (x-2*r),sq_nonneg (x-1),mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ x-1)]
      field_simp
      nlinarith
    have hsrc := hsource (j+1) (by omega)
    calc
      (F j)^2 ≤ Real.exp (-(x-r)^2/(a^2*t)) * ‖cutoffExteriorVector g μ hμ o χ hχ A hA (j+1) (by omega)‖^2 := hs
      _ ≤ Real.exp (-β*x) * (K*x^(2*n)) := mul_le_mul (Real.exp_le_exp.mpr he) hsrc (sq_nonneg _) (Real.exp_pos _).le
      _ = _ := by dsimp only [x]; ring
  have hsq : Tendsto (fun j => (F j)^2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun j => sq_nonneg (F j))) hbound hdecay
  have habs := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero,F] using habs

end Yau.NodeProofs.P06Aux.ExteriorHeat
