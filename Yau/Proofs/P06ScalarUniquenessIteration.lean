import Yau.Proofs.P06ScalarUniquenessEnergy
import Yau.Proofs.P06MetricCutoffs
import Yau.Proofs.P06ScalarUniquenessAlgebra

/-! Finite descent of polynomially growing localized heat energies. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- One genuine local energy step uses the cutoff at twice the radius.
All bounds concern arbitrary solutions in the original PDE class. -/
theorem continuousInitialHeat_cutoff_step
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {u : ℝ → M.Carrier → ℝ}
    (hu : IsContinuousInitialScalarHeat g.form 0 u)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hχ : ∀ j : ℕ, 1 ≤ j → SmoothFn (χ j) ∧ HasCompactSupport (χ j) ∧
      (∀ x, 0 ≤ χ j x ∧ χ j x ≤ 1) ∧
      (∀ x ∈ distBall g.form o j, χ j x = 1) ∧
      tsupport (χ j) ⊆ distBall g.form o (2 * j) ∧
      ∀ x, realGradientNormSq g.form (χ j) x ≤ (c / j) ^ 2)
    {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : 1 ≤ j)
    {A : ℝ} (hA : 0 ≤ A)
    (houter : ∀ t, 0 < t → t ≤ T →
      (∫ x, χ (2 * j) x ^ 2 * u t x ^ 2 ∂μ) ≤ A) :
    ∀ t, 0 < t → t ≤ T → (∫ x, χ j x ^ 2 * u t x ^ 2 ∂μ) ≤
      2 * T * (c / j) ^ 2 * A := by
  have h₁ := hχ j hj
  have h₂ := hχ (2 * j) (by omega)
  have hone : ∀ x ∈ tsupport (χ j), χ (2 * j) x = 1 := by
    intro x hx
    apply h₂.2.2.2.1 x
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h₁.2.2.2.2.1 hx
  have he (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) :
      (∫ x, u s x ^ 2 * scalarGradientPair g.form (χ j) (χ j) x ∂μ) ≤
      (c / j) ^ 2 * A := by
    apply (scalarHeat_cutoff_error_le g μ hμ
      (smoothSpaceTime_slice hu.2.1 hs) h₁.1 h₁.2.1
      h₂.1 h₂.2.1 hone (sq_nonneg _) ?_).trans
      (mul_le_mul_of_nonneg_left (houter s hs hsT) (sq_nonneg _))
    intro x
    simpa only [scalarGradientPair, chartGradientPair_eq_sum, realGradientNormSq] using h₁.2.2.2.2.2 x
  have hh := continuousInitialHeat_cutoff_energy_le g hK μ hμ hu h₁.1 h₁.2.1
    (fun x => by rw [abs_of_nonneg (h₁.2.2.1 x).1]; exact (h₁.2.2.1 x).2)
    (mul_nonneg (sq_nonneg _) hA) hT he
  intro t ht htT
  simpa only [mul_assoc] using hh t ht htT

/-- Polynomial growth of localized energies suffices for uniqueness of an
arbitrary bounded classical heat field with zero continuous initial trace.
The polynomial bound is later supplied by the actual volume comparison. -/
theorem continuousInitialHeat_zero_of_polynomial_energy
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {u : ℝ → M.Carrier → ℝ}
    (hu : IsContinuousInitialScalarHeat g.form 0 u)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ)
    (hbase : ∀ T : ℝ, 0 < T → ∃ D : ℝ, 0 ≤ D ∧
      ∀ j : ℕ, 1 ≤ j → ∀ t, 0 < t → t ≤ T →
        (∫ x, χ j x ^ 2 * u t x ^ 2 ∂μ) ≤ D * (j : ℝ) ^ (2 * n)) :
    ∀ t, 0 < t → u t = 0 := by
  obtain ⟨c, hc, hχ⟩ := hχ
  intro t ht
  obtain ⟨D, hD, hd⟩ := localizedEnergy_power_descent
    (fun j s => ∫ x, χ j x ^ 2 * u s x ^ 2 ∂μ) (2 * n) hc.le ht
    (fun j hj A hA houter => continuousInitialHeat_cutoff_step g hK μ hμ hu o χ hc hχ ht hj hA houter)
    (hbase t ht) (n + 1)
  have hdecay (j : ℕ) (hj : 1 ≤ j) :
      (∫ x, χ j x ^ 2 * u t x ^ 2 ∂μ) ≤ D / (j : ℝ) ^ 2 := by
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have hh := hd j hj t ht le_rfl
    convert hh using 1
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    field_simp
  have hi (j : ℕ) (hj : 1 ≤ j) : Integrable (fun x => χ j x ^ 2 * u t x ^ 2) μ := by
    apply smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow (hχ j hj).1 2)
        (smoothFn_pow (smoothSpaceTime_slice hu.2.1 ht) 2))
    have hs : HasCompactSupport (fun x => χ j x * χ j x) := (hχ j hj).2.1.mul_right
    have hs' : HasCompactSupport (fun x => (χ j x * χ j x) * u t x ^ 2) := hs.mul_right
    simpa only [← pow_two] using hs'
  have hzero (l : ℕ) (hl : 1 ≤ l) : (∫ x, χ l x ^ 2 * u t x ^ 2 ∂μ) = 0 := by
    have hlim : Tendsto (fun j : ℕ => D / (j : ℝ) ^ 2) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop).const_div_atTop D
    apply le_antisymm ?_ (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (max (2 * l) 1)] with j hj
    have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
    have hjl : 2 * l ≤ j := (le_max_left _ _).trans hj
    apply le_trans ?_ (hdecay j hj1)
    apply integral_mono (hi l hl) (hi j hj1)
    intro x
    change χ l x ^ 2 * u t x ^ 2 ≤ χ j x ^ 2 * u t x ^ 2
    by_cases hx : x ∈ tsupport (χ l)
    · have hxball := (hχ l hl).2.2.2.2.1 hx
      have hlj : 0 < (2 * (l : ℝ)) := by
        have : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
        positivity
      have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
      have hmem : x ∈ distBall g.form o j := by
        apply (Yau.LeafProofs.L12Aux.mem_distBall_iff g o x hjpos).mpr
        have hdist := (Yau.LeafProofs.L12Aux.mem_distBall_iff g o x hlj).mp hxball
        have hcast : 2 * (l : ℝ) ≤ j := by exact_mod_cast hjl
        exact hdist.trans_le hcast
      rw [(hχ j hj1).2.2.2.1 x hmem, one_pow, one_mul]
      have hsq : χ l x ^ 2 ≤ 1 := by
        have hr := (hχ l hl).2.2.1 x
        nlinarith
      exact mul_le_of_le_one_left (sq_nonneg _) hsq
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_pow (by omega : 2 ≠ 0), zero_mul]
      positivity
  letI : μ.IsOpenPosMeasure := Yau.LeafProofs.L18Aux.riemannianVolume_isOpenPosMeasure g μ hμ
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
    (Yau.LeafProofs.L12Aux.mem_distBall_iff g o x hpos).mpr (by linarith)
  have heq : (fun y => χ l y ^ 2 * u t y ^ 2) = fun _ => (0 : ℝ) := by
    apply MeasureTheory.Measure.eq_of_ae_eq
      ((integral_eq_zero_iff_of_nonneg (fun y => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hi l hl1)).mp (hzero l hl1))
      (Yau.LeafProofs.L18Aux.continuous_of_smoothFn
        (smoothFn_mul (smoothFn_pow (hχ l hl1).1 2)
          (smoothFn_pow (smoothSpaceTime_slice hu.2.1 ht) 2))) continuous_const
  have hx := congrFun heq x
  rw [(hχ l hl1).2.2.2.1 x hxball, one_pow, one_mul] at hx
  exact sq_eq_zero_iff.mp hx

end Yau.NodeProofs.P06Aux
