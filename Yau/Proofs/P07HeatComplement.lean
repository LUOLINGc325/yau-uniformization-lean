import Yau.Proofs.P07HeatError
import Yau.Proofs.P06ScalarUniquenessRicciPositive

/-! Uniform range and short-time error for every original PDE solution
of a compact-exterior unit-range Lipschitz datum. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L19Aux Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem continuousInitialHeat_unit_range (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (f : Pt X → ℝ) (hc : Continuous (fun x => f x - 1))
    (hcomp : HasCompactSupport (fun x => f x - 1)) (h01 : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (U : ℝ → Pt X → ℝ) (hU : IsContinuousInitialScalarHeat X.metric.form f U)
    {t : ℝ} (ht : 0 < t) (x : Pt X) : U t x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨q, hq, hrep⟩ := continuousInitialHeat_complementary_representation X μ hμ f hc hcomp U hU
  have hq0 : ∀ᵐ y ∂μ, 0 ≤ q y := by
    filter_upwards [hq] with y hy
    rw [hy]
    linarith [(h01 y).2]
  have hq1 : ∀ᵐ y ∂μ, |q y| ≤ 1 := by
    filter_upwards [hq] with y hy
    rw [hy]
    exact abs_le.mpr ⟨by linarith [(h01 y).2], by linarith [(h01 y).1]⟩
  have hp := scalarClassicalHeat_nonneg (complexDimension_pos X.manifold) X.metric
    X.kahler_metric μ hμ q hq0 x ht
  have hb := scalarClassicalHeat_linf (complexDimension_pos X.manifold) X.metric
    X.kahler_metric μ hμ q (K := 1) (by norm_num) hq1 x ht
  rw [hrep t ht x]
  exact ⟨by linarith [le_abs_self (scalarClassicalHeat (complexDimension_pos X.manifold)
    X.metric X.kahler_metric μ hμ q x t)], by linarith⟩

theorem continuousInitialHeat_lipschitz_error (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (f : Pt X → ℝ) (hc : Continuous (fun x => f x - 1))
    (hcomp : HasCompactSupport (fun x => f x - 1)) (h01 : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    {K : ℝ} (hK : 0 < K)
    (hLip : ∀ x y, |f x - f y| ≤ K * inducedDistance X.metric.form x y)
    (U : ℝ → Pt X → ℝ) (hU : IsContinuousInitialScalarHeat X.metric.form f U)
    {t : ℝ} (ht : 0 < t) (x : Pt X) :
    |U t x - f x| ≤ ((n : ℝ) + 1) * K * Real.sqrt t := by
  obtain ⟨q, hq, hrep⟩ := continuousInitialHeat_complementary_representation X μ hμ f hc hcomp U hU
  have hq01 : ∀ y, 1 - f y ∈ Icc (0 : ℝ) 1 := fun y =>
    ⟨by linarith [(h01 y).2], by linarith [(h01 y).1]⟩
  have hqLip : ∀ y z, |(1 - f y) - (1 - f z)| ≤ K * inducedDistance X.metric.form y z := by
    intro y z
    convert hLip y z using 1
    rw [show (1 - f y) - (1 - f z) = -(f y - f z) by ring, abs_neg]
  have he := scalarClassicalHeat_lipschitz_error (complexDimension_pos X.manifold) X.metric
    X.kahler_metric (P06Aux.kahlerManifold_ricci_posSemidef X) μ hμ q (fun y => 1 - f y)
    hq hK hq01 hqLip x ht
  rw [hrep t ht x]
  convert he using 1
  rw [show 1 - scalarClassicalHeat (complexDimension_pos X.manifold) X.metric X.kahler_metric μ hμ q x t - f x =
    -(scalarClassicalHeat (complexDimension_pos X.manifold) X.metric X.kahler_metric μ hμ q x t - (1 - f x)) by ring,
    abs_neg]

/-- The common time factor is chosen before every spatial scale. -/
theorem exists_uniform_heat_time (n : ℕ) {K0 : ℝ} (hK0 : 0 < K0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ L : ℝ, 0 < L →
      ((n : ℝ) + 1) * (K0 / L) * Real.sqrt (ε * L ^ 2) = 1 / 16 := by
  let D := 16 * ((n : ℝ) + 1) * K0
  have hD : 0 < D := by dsimp only [D]; positivity
  let ε := D⁻¹ ^ 2
  refine ⟨ε, by dsimp only [ε]; positivity, ?_⟩
  intro L hL
  have hsq : ε * L ^ 2 = (L / D) ^ 2 := by dsimp only [ε]; ring
  rw [hsq, Real.sqrt_sq (div_pos hL hD).le]
  dsimp only [D]
  field_simp
  <;> ring

end Yau.NodeProofs.P07Aux
