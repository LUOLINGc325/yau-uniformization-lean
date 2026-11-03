import Yau.Proofs.P06HodgeDaviesWeighted
import Yau.Proofs.P06MetricCutoffs

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.Davies
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Actual restriction in the form Hilbert space, implemented by the
bounded measurable scalar indicator on the original completion. -/
def indicator (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  multiplyL2FormHilbert g μ (s.indicator (fun _ => (1 : ℝ)))
    (stronglyMeasurable_const.indicator hs).aestronglyMeasurable
    1 zero_le_one (fun x => by by_cases hx : x ∈ s <;> simp [hx])

/-- A supplied genuine annular cutoff yields an arbitrary exponential
tail parameter for the actual all-degree Hodge heat. -/
theorem heat_annular_weighted_tail (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (r R : ℝ) (hr : 0 < r)
    (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (hηrange : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hηone : ∀ x, inducedDistance g.form o x ≤ r → η x = 1)
    (hηsupport : tsupport η ⊆ distBall g.form o R)
    (A : ℝ) (hηgrad : ∀ x, L18Aux.scalarGradientPair g.form η η x ≤ (A / (R - r)) ^ 2)
    (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) (ht : 0 ≤ t)
    (f : L2FormHilbert g μ k)
    (hf : indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) f = f) :
    ‖indicator g μ (distBall g.form o R)ᶜ (L12Aux.measurableSet_distBall g o R).compl
        (hodgeHeatHilbert g μ hμ k t f)‖ ≤
      Real.exp (-lam + (lam * A / (R - r)) ^ 2 * t / 2) * ‖f‖ := by
  let ψ := fun x => lam * (1 - η x)
  have hψ : SmoothFn ψ := fun x => (contDiffOn_const.mul ((contDiffOn_const).sub (hη x)))
  have hb (x : M.Carrier) : ψ x ≤ lam := by
    dsimp only [ψ]
    nlinarith [mul_nonneg hlam (hηrange x).1]
  have hgrad (x : M.Carrier) : L18Aux.scalarGradientPair g.form ψ ψ x ≤
      (lam * A / (R - r)) ^ 2 := by
    have hF : HasDerivAt (fun q : ℝ => lam * (1 - q)) (-lam) (η x) := by
      simpa only [Pi.sub_apply, id_eq, zero_sub, mul_neg, mul_one] using
        (((hasDerivAt_const (η x) (1 : ℝ)).sub (hasDerivAt_id (η x))).const_mul lam)
    dsimp only [ψ]
    rw [L18Aux.scalarGradientPair_scalar_comp_self g.form hη
      (fun q : ℝ => lam * (1 - q)) x hF.differentiableAt, hF.deriv]
    have hh := mul_le_mul_of_nonneg_left (hηgrad x) (sq_nonneg lam)
    nlinarith [show (lam * A / (R - r)) ^ 2 = lam ^ 2 * (A / (R - r)) ^ 2 by ring]
  let W := expMultiplier (k := k) g μ ψ hψ lam hb
  let sin := distBall g.form o r
  let sout := (distBall g.form o R)ᶜ
  have hin : MeasurableSet sin := L12Aux.measurableSet_distBall g o r
  have hout : MeasurableSet sout := (L12Aux.measurableSet_distBall g o R).compl
  have hiB (x : M.Carrier) : |sin.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ sin <;> simp [hx]
  have hoB (x : M.Carrier) : |sout.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ sout <;> simp [hx]
  have heB (x : M.Carrier) : |Real.exp (ψ x)| ≤ Real.exp lam := by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (hb x)
  have hWf : W f = f := by
    have heq (x : M.Carrier) : Real.exp (ψ x) * sin.indicator (fun _ => (1 : ℝ)) x =
        sin.indicator (fun _ => (1 : ℝ)) x := by
      by_cases hx : x ∈ sin
      · have he := hηone x ((L12Aux.mem_distBall_iff g o x hr).mp hx).le
        simp [Set.indicator_of_mem hx, ψ, he]
      · simp [Set.indicator_of_notMem hx]
    have hc := multiplier_comp_eq g μ (fun x => Real.exp (ψ x))
      (sin.indicator (fun _ => (1 : ℝ))) (sin.indicator (fun _ => (1 : ℝ)))
      (L18Aux.continuous_of_smoothFn
        (L18Aux.smoothFn_scalar_comp hψ Real.exp Real.contDiff_exp)).aestronglyMeasurable
      (stronglyMeasurable_const.indicator hin).aestronglyMeasurable
      (stronglyMeasurable_const.indicator hin).aestronglyMeasurable
      (Real.exp lam) 1 1 (Real.exp_pos _).le zero_le_one zero_le_one heB hiB hiB heq f
    change W (indicator g μ sin hin f) = indicator g μ sin hin f at hc
    rwa [hf] at hc
  have htail : ‖indicator g μ sout hout (hodgeHeatHilbert g μ hμ k t f)‖ ≤
      Real.exp (-lam) * ‖W (hodgeHeatHilbert g μ hμ k t f)‖ := by
    apply multiplier_norm_compare g μ (sout.indicator (fun _ => (1 : ℝ)))
      (fun x => Real.exp (ψ x))
      (stronglyMeasurable_const.indicator hout).aestronglyMeasurable
      (L18Aux.continuous_of_smoothFn
        (L18Aux.smoothFn_scalar_comp hψ Real.exp Real.contDiff_exp)).aestronglyMeasurable
      1 (Real.exp lam) zero_le_one (Real.exp_pos _).le hoB heB
      (Real.exp (-lam)) (Real.exp_pos _).le (fun x => ?_)
    by_cases hx : x ∈ sout
    · have he : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηsupport h))
      simp only [Set.indicator_of_mem hx, abs_one, abs_of_pos (Real.exp_pos _), ψ,
        he, sub_zero, mul_one]
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      positivity
  have hw := heat_weighted_L2 g μ hμ ψ hψ lam hb (lam * A / (R - r)) hgrad t ht f
  change ‖W (hodgeHeatHilbert g μ hμ k t f)‖ ≤ _ at hw
  rw [hWf] at hw
  calc
    _ ≤ Real.exp (-lam) * ‖W (hodgeHeatHilbert g μ hμ k t f)‖ := htail
    _ ≤ Real.exp (-lam) * (Real.exp ((lam * A / (R - r)) ^ 2 * t / 2) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]

/-- The annular Gaussian estimate is uniform in metric, measure, form
 degree and input. Its constant is the actual dimensional L18 cutoff
constant, with no curvature or auxiliary solution assumption. -/
theorem exists_uniform_annular_heat_L2_tail (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (k : ℕ)
      (o : M.Carrier) (r R : ℝ), 0 < r → r < R →
      ∀ (t : ℝ), 0 < t → ∀ (f : L2FormHilbert g μ k),
      (indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) f = f) →
      ‖indicator g μ (distBall g.form o R)ᶜ (L12Aux.measurableSet_distBall g o R).compl
        (hodgeHeatHilbert g μ hμ k t f)‖ ≤
        Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖ := by
  obtain ⟨C, hC, hcuts⟩ := L18Aux.exists_uniform_annular_scalar_energy_cutoffs n
  let A := max 1 C
  have hA : 1 ≤ A := le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨A, hA, ?_⟩
  intro M g μ hμ k o r R hr hrR t ht f hf
  obtain ⟨η, _, hη, _, hηrange, hηone, hηsupport, hηgrad⟩ := hcuts M g o r R hr hrR
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hηA (x : M.Carrier) : L18Aux.scalarGradientPair g.form η η x ≤ (A / (R - r)) ^ 2 := by
    apply (hηgrad x).trans
    apply (sq_le_sq₀ (div_nonneg hC.le hd.le) (div_nonneg hApos.le hd.le)).2
    exact div_le_div_of_nonneg_right (le_max_right 1 C) hd.le
  let lam := (R - r) ^ 2 / (A ^ 2 * t)
  have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
  have hw := heat_annular_weighted_tail g μ hμ o r R hr η hη hηrange
    hηone hηsupport A hηA lam hlam t ht.le f hf
  have he : -lam + (lam * A / (R - r)) ^ 2 * t / 2 =
      -(R - r) ^ 2 / (2 * A ^ 2 * t) := by
    dsimp only [lam]
    field_simp [ne_of_gt hd, ne_of_gt hApos, ne_of_gt ht]
    ring
  rwa [he] at hw

end Yau.NodeProofs.P06Aux.Davies
