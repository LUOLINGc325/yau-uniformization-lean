import Yau.LeafProofs.L19HeatWeightedEnergyExponential

/-! Annular Davies--Gaffney decay, using genuine dimensional scalar cutoffs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Restriction to a measurable set, in the original scalar L² space. -/
def scalarL2Indicator {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)

theorem scalarL2Indicator_coe {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    scalarL2Indicator μ s hs f =ᵐ[μ] s.indicator f :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp

theorem scalarHeatFamily_annular_weighted_tail (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (r R : ℝ) (hr : 0 < r) (_hrR : r < R)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hηrange : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hηone : ∀ x, inducedDistance g.form o x ≤ r → η x = 1)
    (hηsupport : tsupport η ⊆ distBall g.form o R)
    (A : ℝ) (hηgrad : ∀ x, scalarGradientPair g.form η η x ≤ (A / (R - r)) ^ 2)
    (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ distBall g.form o r → f x = 0) :
    ‖scalarL2Indicator μ (distBall g.form o R)ᶜ (L12Aux.measurableSet_distBall g o R).compl
        (scalarHeatFamily g μ hμ t f)‖ ≤
      Real.exp (-lam + (lam * A / (R - r)) ^ 2 * t / 2) * ‖f‖ := by
  let ψ := fun x => lam * (1 - η x)
  have hψ : SmoothFn ψ := smoothFn_mul (smoothFn_const lam)
    (smoothFn_sub (smoothFn_const 1) hη)
  have hb (x : M.Carrier) : ψ x ≤ lam := by
    dsimp only [ψ]
    nlinarith [mul_nonneg hlam (hηrange x).1]
  have hgrad (x : M.Carrier) : scalarGradientPair g.form ψ ψ x ≤
      (lam * A / (R - r)) ^ 2 := by
    have hF : HasDerivAt (fun q : ℝ => lam * (1 - q)) (-lam) (η x) := by
      simpa only [Pi.sub_apply, id_eq, zero_sub, mul_neg, mul_one] using
        (((hasDerivAt_const (η x) (1 : ℝ)).sub (hasDerivAt_id (η x))).const_mul lam)
    dsimp only [ψ]
    rw [scalarGradientPair_scalar_comp_self g.form hη (fun q : ℝ => lam * (1 - q)) x
      hF.differentiableAt, hF.deriv]
    have hh := mul_le_mul_of_nonneg_left (hηgrad x) (sq_nonneg lam)
    nlinarith [show (lam * A / (R - r)) ^ 2 = lam ^ 2 * (A / (R - r)) ^ 2 by ring]
  let W := scalarExpMultiplierL2 μ ψ hψ lam hb
  have hWf : W f = f := by
    apply Lp.ext
    filter_upwards [scalarExpMultiplierL2_coe μ ψ hψ lam hb f, hf] with x hx hfx
    change W f x = _ at hx ⊢
    rw [hx]
    by_cases hxr : x ∈ distBall g.form o r
    · have he := hηone x ((L12Aux.mem_distBall_iff g o x hr).mp hxr).le
      simp [ψ, he]
    · rw [hfx hxr, mul_zero]
  have htail : ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
      (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t f)‖ ≤
      Real.exp (-lam) * ‖W (scalarHeatFamily g μ hμ t f)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [scalarL2Indicator_coe μ (distBall g.form o R)ᶜ
      (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t f),
      scalarExpMultiplierL2_coe μ ψ hψ lam hb (scalarHeatFamily g μ hμ t f)] with x hi hw
    rw [hi, hw]
    by_cases hx : x ∈ (distBall g.form o R)ᶜ
    · have he : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηsupport h))
      rw [Set.indicator_of_mem hx]
      simp only [ψ, he, sub_zero, mul_one, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hc : Real.exp (-lam) * Real.exp lam = 1 := by rw [← Real.exp_add]; simp
      rw [← mul_assoc, hc, one_mul]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hw := scalarHeatFamily_weighted_L2 g μ hμ ψ hψ lam hb (lam * A / (R - r)) hgrad t ht f
  change ‖W (scalarHeatFamily g μ hμ t f)‖ ≤ _ at hw
  rw [hWf] at hw
  calc
    _ ≤ Real.exp (-lam) * ‖W (scalarHeatFamily g μ hμ t f)‖ := htail
    _ ≤ Real.exp (-lam) * (Real.exp ((lam * A / (R - r)) ^ 2 * t / 2) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]

/-- The dimensional cutoff constant is chosen before the metric and
measure. The tail estimate is for the actual heat operator and every L²
input supported almost everywhere in the inner ball. -/
theorem exists_uniform_annular_heat_L2_tail (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
      (o : M.Carrier) (r R : ℝ), 0 < r → r < R →
      ∀ (t : ℝ), 0 < t → ∀ (f : Lp ℝ 2 μ),
      (∀ᵐ x ∂μ, x ∉ distBall g.form o r → f x = 0) →
      ‖scalarL2Indicator μ (distBall g.form o R)ᶜ (L12Aux.measurableSet_distBall g o R).compl
        (scalarHeatFamily g μ hμ t f)‖ ≤
        Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖ := by
  obtain ⟨C, hC, hcuts⟩ := exists_uniform_annular_scalar_energy_cutoffs n
  let A := max 1 C
  have hA : 1 ≤ A := le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨A, hA, ?_⟩
  intro M g μ hμ o r R hr hrR t ht f hf
  obtain ⟨η, _, hη, _, hηrange, hηone, hηsupport, hηgrad⟩ := hcuts M g o r R hr hrR
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hηA (x : M.Carrier) : scalarGradientPair g.form η η x ≤ (A / (R - r)) ^ 2 := by
    apply (hηgrad x).trans
    apply (sq_le_sq₀ (div_nonneg hC.le hd.le) (div_nonneg hApos.le hd.le)).2
    exact div_le_div_of_nonneg_right (le_max_right 1 C) hd.le
  let lam := (R - r) ^ 2 / (A ^ 2 * t)
  have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
  have hw := scalarHeatFamily_annular_weighted_tail g μ hμ o r R hr hrR η hη hηrange
    hηone hηsupport A hηA lam hlam t ht.le f hf
  have he : -lam + (lam * A / (R - r)) ^ 2 * t / 2 =
      -(R - r) ^ 2 / (2 * A ^ 2 * t) := by
    dsimp only [lam]
    field_simp [ne_of_gt hd, ne_of_gt hApos, ne_of_gt ht]
    ring
  rwa [he] at hw

end Yau.LeafProofs.L19Aux
