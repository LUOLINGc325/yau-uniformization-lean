import Yau.Proofs.P06FormUniquenessEnergy
import Yau.Proofs.P06MetricCutoffs
import Yau.Proofs.P06ScalarUniquenessAlgebra

/-! Finite cutoff descent for the actual metric norm of form heat. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}

theorem formHeat_cutoff_error_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {W : RealForm M k} (hW : SmoothRealForm W)
    {η ψ : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ)
    (hone : ∀ x ∈ tsupport η, ψ x = 1)
    {a : ℝ} (ha : 0 ≤ a)
    (hgrad : ∀ x, L18Aux.scalarGradientPair g.form η η x ≤ a) :
    (∫ x, L18Aux.scalarGradientPair g.form η η x * formNormSq g.form W x ∂μ) ≤
      a * ∫ x, ψ x ^ 2 * formNormSq g.form W x ∂μ := by
  have hn : SmoothFn (formNormSq g.form W) :=
    G04Aux.formInner_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g) W W hW hW
  have hi : Integrable (fun x => L18Aux.scalarGradientPair g.form η η x * formNormSq g.form W x) μ :=
    L18Aux.smoothFn_integrable_compact g μ hμ
      (L18Aux.smoothFn_mul (L18Aux.smoothFn_scalarGradientPair g hη hη) hn)
      (L18Aux.scalarGradientPair_hasCompactSupport g.form η η hcη).mul_right
  have hj : Integrable (fun x => ψ x ^ 2 * formNormSq g.form W x) μ :=
    L18Aux.smoothFn_integrable_compact g μ hμ
      (L18Aux.smoothFn_mul (L18Aux.smoothFn_pow hψ 2) hn)
      (by
        have hs : HasCompactSupport (fun x => ψ x * ψ x) := hcψ.mul_right
        simpa only [Pi.mul_def, ← pow_two] using (hs.mul_right :
          HasCompactSupport (fun x => (ψ x * ψ x) * formNormSq g.form W x)))
  rw [← integral_const_mul]
  apply integral_mono hi (hj.const_mul a)
  intro x
  change L18Aux.scalarGradientPair g.form η η x * formNormSq g.form W x ≤
    a * (ψ x ^ 2 * formNormSq g.form W x)
  by_cases hx : x ∈ tsupport η
  · simpa only [hone x hx, one_pow, one_mul] using
      mul_le_mul_of_nonneg_right (hgrad x) (L03.formNormSq_nonneg _ _ _)
  · rw [L18Aux.scalarGradientPair_zero_of_notMem_tsupport g.form η η hx, zero_mul]
    exact mul_nonneg ha (mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _))

theorem boundedFormHeat_difference_cutoff_step
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {A : RealForm M k} {U V : ℝ → RealForm M k}
    (hU : IsBoundedFormHeat g.form A U) (hV : IsBoundedFormHeat g.form A V)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hχ : ∀ j : ℕ, 1 ≤ j → SmoothFn (χ j) ∧ HasCompactSupport (χ j) ∧
      (∀ x, 0 ≤ χ j x ∧ χ j x ≤ 1) ∧
      (∀ x ∈ distBall g.form o j, χ j x = 1) ∧
      tsupport (χ j) ⊆ distBall g.form o (2 * j) ∧
      ∀ x, realGradientNormSq g.form (χ j) x ≤ (c / j) ^ 2)
    {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : 1 ≤ j)
    {B : ℝ} (hB : 0 ≤ B)
    (houter : ∀ t, 0 < t → t ≤ T →
      (∫ x, χ (2 * j) x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) ≤ B) :
    ∀ t, 0 < t → t ≤ T →
      (∫ x, χ j x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) ≤
        2 * T * (c / j) ^ 2 * B := by
  have h₁ := hχ j hj
  have h₂ := hχ (2 * j) (by omega)
  have hone : ∀ x ∈ tsupport (χ j), χ (2 * j) x = 1 := by
    intro x hx
    apply h₂.2.2.2.1 x
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h₁.2.2.2.2.1 hx
  have he (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) :
      (∫ x, L18Aux.scalarGradientPair g.form (χ j) (χ j) x *
        formNormSq g.form (U s - V s) x ∂μ) ≤ (c / j) ^ 2 * B := by
    apply (formHeat_cutoff_error_le g μ hμ
      (smoothFormTime_slice (smoothFormTime_sub hU.1 hV.1) hs)
      h₁.1 h₁.2.1 h₂.1 h₂.2.1 hone (sq_nonneg _) ?_).trans
        (mul_le_mul_of_nonneg_left (houter s hs hsT) (sq_nonneg _))
    intro x
    simpa only [L18Aux.scalarGradientPair, L18Aux.chartGradientPair_eq_sum,
      realGradientNormSq] using h₁.2.2.2.2.2 x
  have hh := boundedFormHeat_difference_cutoff_energy_le g μ hμ hU hV h₁.1 h₁.2.1
    (fun x => by rw [abs_of_nonneg (h₁.2.2.1 x).1]; exact (h₁.2.2.1 x).2)
    (mul_nonneg (sq_nonneg _) hB) hT he
  intro t ht htT
  simpa only [mul_assoc] using hh t ht htT

/-- A finite number of genuine d/δ cutoff estimates beats the polynomial
volume growth. Continuity and full support recover equality at each point. -/
theorem boundedFormHeat_unique_of_polynomial_energy
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {A : RealForm M k} {U V : ℝ → RealForm M k}
    (hU : IsBoundedFormHeat g.form A U) (hV : IsBoundedFormHeat g.form A V)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ)
    (hbase : ∀ T : ℝ, 0 < T → ∃ D : ℝ, 0 ≤ D ∧
      ∀ j : ℕ, 1 ≤ j → ∀ t, 0 < t → t ≤ T →
        (∫ x, χ j x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) ≤
          D * (j : ℝ) ^ (2 * n)) :
    ∀ t, 0 < t → U t = V t := by
  obtain ⟨c, hc, hχ⟩ := hχ
  intro t ht
  obtain ⟨D, hD, hd⟩ := localizedEnergy_power_descent
    (fun j s => ∫ x, χ j x ^ 2 * formNormSq g.form (U s - V s) x ∂μ)
    (2 * n) hc.le ht
    (fun j hj B hB houter => boundedFormHeat_difference_cutoff_step g μ hμ hU hV o χ hc hχ ht hj hB houter)
    (hbase t ht) (n + 1)
  have hdecay (j : ℕ) (hj : 1 ≤ j) :
      (∫ x, χ j x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) ≤ D / (j : ℝ) ^ 2 := by
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have hh := hd j hj t ht le_rfl
    convert hh using 1
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    field_simp
  have hi (j : ℕ) (hj : 1 ≤ j) :
      Integrable (fun x => χ j x ^ 2 * formNormSq g.form (U t - V t) x) μ := by
    apply L18Aux.smoothFn_integrable_compact g μ hμ
      (L18Aux.smoothFn_mul (L18Aux.smoothFn_pow (hχ j hj).1 2)
        (L19Aux.smoothSpaceTime_slice
          (smoothFormTime_normSq g (smoothFormTime_sub hU.1 hV.1)) ht))
    have hs : HasCompactSupport (fun x => χ j x * χ j x) := (hχ j hj).2.1.mul_right
    simpa only [Pi.mul_def, ← pow_two] using (hs.mul_right :
      HasCompactSupport (fun x => (χ j x * χ j x) * formNormSq g.form (U t - V t) x))
  have hzero (l : ℕ) (hl : 1 ≤ l) :
      (∫ x, χ l x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) = 0 := by
    have hlim : Tendsto (fun j : ℕ => D / (j : ℝ) ^ 2) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop).const_div_atTop D
    apply le_antisymm ?_ (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _)))
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (max (2 * l) 1)] with j hj
    have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
    have hjl : 2 * l ≤ j := (le_max_left _ _).trans hj
    apply le_trans ?_ (hdecay j hj1)
    apply integral_mono (hi l hl) (hi j hj1)
    intro x
    change χ l x ^ 2 * formNormSq g.form (U t - V t) x ≤
      χ j x ^ 2 * formNormSq g.form (U t - V t) x
    by_cases hx : x ∈ tsupport (χ l)
    · have hxball := (hχ l hl).2.2.2.2.1 hx
      have hlpos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have hmem : x ∈ distBall g.form o j := by
        apply (L12Aux.mem_distBall_iff g o x hjpos).mpr
        have hdist := (L12Aux.mem_distBall_iff g o x (by positivity : 0 < 2 * (l : ℝ))).mp hxball
        exact hdist.trans_le (by exact_mod_cast hjl)
      rw [(hχ j hj1).2.2.2.1 x hmem, one_pow, one_mul]
      have hsq : χ l x ^ 2 ≤ 1 := by
        have hr := (hχ l hl).2.2.1 x
        nlinarith
      exact mul_le_of_le_one_left (L03.formNormSq_nonneg _ _ _) hsq
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_pow (by omega : 2 ≠ 0), zero_mul]
      exact mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _)
  letI : μ.IsOpenPosMeasure := L18Aux.riemannianVolume_isOpenPosMeasure g μ hμ
  funext x
  obtain ⟨l, hl⟩ := exists_nat_gt (inducedDistance g.form o x + 1)
  have hl1 : 1 ≤ l := by
    have hh := g.induced_distance_nonneg o x
    by_contra hh'
    have : l = 0 := by omega
    subst l
    norm_num at hl
    linarith
  have hpos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hxball : x ∈ distBall g.form o l :=
    (L12Aux.mem_distBall_iff g o x hpos).mpr (by linarith)
  have heq : (fun y => χ l y ^ 2 * formNormSq g.form (U t - V t) y) = fun _ => (0 : ℝ) := by
    apply MeasureTheory.Measure.eq_of_ae_eq
      ((integral_eq_zero_iff_of_nonneg
        (fun y => mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _)) (hi l hl1)).mp (hzero l hl1))
      (L18Aux.continuous_of_smoothFn
        (L18Aux.smoothFn_mul (L18Aux.smoothFn_pow (hχ l hl1).1 2)
          (L19Aux.smoothSpaceTime_slice
            (smoothFormTime_normSq g (smoothFormTime_sub hU.1 hV.1)) ht))) continuous_const
  have hx := congrFun heq x
  rw [(hχ l hl1).2.2.2.1 x hxball, one_pow, one_mul] at hx
  exact sub_eq_zero.mp ((L03.formNormSq_eq_zero_iff g.form (U t - V t) x).mp hx)

end Yau.NodeProofs.P06Aux
