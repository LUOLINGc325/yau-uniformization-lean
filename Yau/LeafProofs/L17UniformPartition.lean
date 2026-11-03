import Yau.LeafProofs.L17AtlasPartition

/-!
Geometric partition data constructed from the original bounded-geometry
hypothesis. Quantitative jet bounds are separate properties of these functions.
-/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

structure UniformChartPartition (g : HermitianField M) where
  charts : BoundedChartFamily g
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < charts.radius
  Index : Type
  index_countable : Countable Index
  center : Index → M.Carrier
  overlapBudget : ℕ
  separated : (Set.range center).Pairwise
    (fun p q => coverScale charts * radius ≤ inducedDistance g p q)
  covers : ∀ x : M.Carrier, ∃ p ∈ Set.range center,
    x ∈ charts.chart p '' ball 0 (radius / 4)
  overlap : ∀ x : M.Carrier, ∃ V ∈ 𝓝 x,
    {p : Set.range center | ((charts.chart p '' closedBall 0 radius) ∩ V).Nonempty}.Finite ∧
    Nat.card {p : Set.range center |
      ((charts.chart p '' closedBall 0 radius) ∩ V).Nonempty} ≤ overlapBudget

namespace UniformChartPartition

variable {g : HermitianField M} (P : UniformChartPartition g)

def centers : Set M.Carrier := Set.range P.center

theorem centers_countable : P.centers.Countable := by
  let := P.index_countable
  exact Set.countable_range P.center

end UniformChartPartition

theorem BoundedChartFamily.exists_uniform_partition_below
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : UniformChartPartition g, P.charts = A ∧ P.radius < ε := by
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  let L := overlapScale A
  have hC := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  have hL : 0 < L := overlapScale_pos A
  let ρ := min (ε / 2) (min (A.radius / 2) (c * A.radius / (8 * L)))
  have hr := A.radius_pos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < A.radius :=
    (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt (by linarith)
  have hρε : ρ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hρL : ρ ≤ c * A.radius / (8 * L) := (min_le_right _ _).trans (min_le_right _ _)
  have hbudget : L * ρ < c * (A.radius / 2) := by
    calc
      L * ρ ≤ L * (c * A.radius / (8 * L)) := mul_le_mul_of_nonneg_left hρL hL.le
      _ = c * A.radius / 8 := by field_simp
      _ < c * (A.radius / 2) := by nlinarith [mul_pos hc hr]
  obtain ⟨N, hN⟩ := A.exists_uniform_net_cover hg
  obtain ⟨S, hcount, hsep, hcover, hover⟩ := hN ρ hρ hρr hbudget
  let := hcount.to_subtype
  refine ⟨⟨A, ρ, hρ, hρr, S, inferInstance, Subtype.val, N, ?_, ?_, ?_⟩, rfl, hρε⟩
  · simpa only [Subtype.range_val] using hsep
  · simpa only [Subtype.range_val] using hcover
  · rw [show Set.range (Subtype.val : S → M.Carrier) = S from Subtype.range_val]
    exact hover

namespace UniformChartPartition

variable {g : HermitianField M} (P : UniformChartPartition g)

theorem locallyFinite : LocallyFinite (fun p : P.centers => P.charts.chart p '' closedBall 0 P.radius) := by
  intro x
  obtain ⟨V, hV, hfinite, _⟩ := P.overlap x
  exact ⟨V, hV, hfinite⟩

def weight (p : P.centers) : M.Carrier → ℝ :=
  normalizedChartWeight P.charts P.centers P.radius P.radius_pos p

def localization (p : P.centers) : M.Carrier → ℝ :=
  chartLocalization (P.charts.chart p) P.radius P.radius_pos

theorem weight_smooth (p : P.centers) : SmoothFn (P.weight p) :=
  P.charts.normalizedChartWeight_smooth P.centers P.radius_pos P.radius_lt P.covers P.locallyFinite p

theorem weight_hasCompactSupport (p : P.centers) : HasCompactSupport (P.weight p) :=
  P.charts.normalizedChartWeight_hasCompactSupport P.centers P.radius_pos P.radius_lt p

theorem weight_nonneg (p : P.centers) (x : M.Carrier) : 0 ≤ P.weight p x :=
  P.charts.normalizedChartWeight_nonneg P.centers P.radius_pos p x

theorem weight_le_one (p : P.centers) (x : M.Carrier) : P.weight p x ≤ 1 :=
  P.charts.normalizedChartWeight_le_one P.centers P.radius_pos P.radius_lt P.covers P.locallyFinite p x

theorem weight_sum (x : M.Carrier) : (∑ᶠ p : P.centers, P.weight p x) = 1 :=
  P.charts.normalizedChartWeight_sum P.centers P.radius_pos P.radius_lt P.covers P.locallyFinite x

theorem localization_smooth (p : P.centers) : SmoothFn (P.localization p) :=
  (P.charts.chartLocalization_properties p P.radius_pos P.radius_lt).2.1

theorem localization_hasCompactSupport (p : P.centers) : HasCompactSupport (P.localization p) :=
  (P.charts.chartLocalization_properties p P.radius_pos P.radius_lt).1

theorem localization_mul_weight (p : P.centers) (x : M.Carrier) :
    P.localization p x * P.weight p x = P.weight p x :=
  P.charts.chartLocalization_mul_normalizedWeight P.centers P.radius_pos P.radius_lt p x

end UniformChartPartition

theorem exists_uniformChartPartition
    (g : HermitianField M) (hg : MetricSmooth g)
    (hbg : LeafCandidates.HermitianBoundedGeometry g) : Nonempty (UniformChartPartition g) := by
  obtain ⟨A⟩ := exists_boundedChartFamily g hbg
  obtain ⟨P, _, _⟩ := A.exists_uniform_partition_below hg (by norm_num : (0 : ℝ) < 1)
  exact ⟨P⟩

end Yau.LeafProofs.L17Aux
