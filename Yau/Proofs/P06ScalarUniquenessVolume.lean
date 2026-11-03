import Yau.Proofs.P06ScalarUniquenessIteration
import Yau.LeafProofs.L12Complete

/-! Volume comparison supplies the initial polynomial energy bound. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux Yau.LeafProofs.L19Aux
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem distBall_measure_lt_top (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {r : ℝ} (hr : 0 < r) :
    μ (distBall g.form o r) < ⊤ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  apply lt_of_le_of_lt (measure_mono (t := {x | inducedDistance g.form o x ≤ r}) ?_)
    (isCompact_inducedDistance_sublevel g o r).measure_lt_top
  intro x hx
  exact ((mem_distBall_iff g o x hr).mp hx).le

/-- The exact proved Bishop--Gromov theorem gives the needed polynomial
growth for the actual Riemannian measure and original metric balls. -/
theorem distBall_real_volume_polynomial
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) {r : ℝ} (hr : 1 ≤ r) :
    μ.real (distBall g.form o r) ≤ r ^ (2 * n) * μ.real (distBall g.form o 1) := by
  have hv := Yau.LeafProofs.L12 n M g g.complete_distance hK hRic μ hμ o 1 r zero_lt_one hr
  rw [div_one] at hv
  have hfin : ENNReal.ofReal (r ^ (2 * n)) * μ (distBall g.form o 1) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (distBall_measure_lt_top g μ hμ o zero_lt_one).ne
  have hh := ENNReal.toReal_mono hfin hv
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ (2 * n))] using hh

/-- A bounded field and the actual polynomial volume bound give the base
case for the finite energy descent. -/
theorem continuousInitialHeat_polynomial_energy
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : ℝ → M.Carrier → ℝ}
    (hu : IsContinuousInitialScalarHeat g.form 0 u)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ) :
    ∀ T : ℝ, 0 < T → ∃ D : ℝ, 0 ≤ D ∧
      ∀ j : ℕ, 1 ≤ j → ∀ t, 0 < t → t ≤ T →
        (∫ x, χ j x ^ 2 * u t x ^ 2 ∂μ) ≤ D * (j : ℝ) ^ (2 * n) := by
  obtain ⟨c, hc, hχ⟩ := hχ
  intro T hT
  obtain ⟨B, hB, hb⟩ := hu.2.2.2.1 T hT
  refine ⟨B ^ 2 * (2 : ℝ) ^ (2 * n) * μ.real (distBall g.form o 1), by positivity, ?_⟩
  intro j hj t ht htT
  have hcut := hχ j hj
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have heq : (∫ x in distBall g.form o (2 * j), χ j x ^ 2 * u t x ^ 2 ∂μ) =
      ∫ x, χ j x ^ 2 * u t x ^ 2 ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x ∉ tsupport (χ j) := fun h => hx (hcut.2.2.2.2.1 h)
    simp only [image_eq_zero_of_notMem_tsupport hx', zero_pow (by omega : 2 ≠ 0), zero_mul]
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (distBall_measure_lt_top g μ hμ o (by positivity : 0 < 2 * (j : ℝ)))
    (f := fun x => χ j x ^ 2 * u t x ^ 2) (C := B ^ 2) (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hsq : χ j x ^ 2 ≤ 1 := by
        have hr := hcut.2.2.1 x
        nlinarith
      have huB : u t x ^ 2 ≤ B ^ 2 := by
        have hbound := hb x t ht htT
        nlinarith [sq_abs (u t x), abs_nonneg (u t x)]
      exact (mul_le_of_le_one_left (sq_nonneg _) hsq).trans huB)
  rw [heq, Real.norm_eq_abs] at hnorm
  have hrad : 1 ≤ 2 * (j : ℝ) := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hvol := distBall_real_volume_polynomial g hK hRic μ hμ o hrad
  calc
    _ ≤ B ^ 2 * μ.real (distBall g.form o (2 * j)) := (le_abs_self _).trans hnorm
    _ ≤ B ^ 2 * ((2 * (j : ℝ)) ^ (2 * n) * μ.real (distBall g.form o 1)) :=
      mul_le_mul_of_nonneg_left hvol (sq_nonneg _)
    _ = _ := by rw [mul_pow]; ring

/-- Uniqueness for arbitrary bounded classical scalar heat under the
ordinary nonnegative Ricci hypothesis, with the original continuous trace. -/
theorem continuousInitialScalarHeat_unique_of_nonnegativeRicci
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : M.Carrier → ℝ) (u v : ℝ → M.Carrier → ℝ)
    (hu : IsContinuousInitialScalarHeat g.form f u)
    (hv : IsContinuousInitialScalarHeat g.form f v) :
    ∀ t, 0 < t → u t = v t := by
  have hw : IsContinuousInitialScalarHeat g.form 0 (fun t x => u t x - v t x) := by
    simpa only [sub_self, Pi.zero_def] using continuousInitialHeat_sub hu hv
  intro t ht
  funext x
  obtain ⟨χ, hχ⟩ := metricCutoffFamily g x
  have hzero := continuousInitialHeat_zero_of_polynomial_energy g hK μ hμ hw x χ hχ
    (continuousInitialHeat_polynomial_energy g hK hRic μ hμ hw x χ hχ) t ht
  exact sub_eq_zero.mp (congrFun hzero x)

end Yau.NodeProofs.P06Aux
