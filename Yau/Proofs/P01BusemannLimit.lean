import Mathlib

noncomputable section
open Filter
open scoped Topology NNReal

namespace Yau.NodeProofs.P01Aux
variable {E : Type*} [MetricSpace E]

def signedDistanceSequence (o : E) (ray : ℝ≥0 → E) (x : E) (j : ℕ) : ℝ :=
  dist o (ray j) - dist x (ray j)

theorem signedDistanceSequence_bounds (o : E) (ray : ℝ≥0 → E) (x : E) (j : ℕ) :
    -dist o x ≤ signedDistanceSequence o ray x j ∧
      signedDistanceSequence o ray x j ≤ dist o x := by
  dsimp [signedDistanceSequence]
  constructor
  · have h := dist_triangle x o (ray j)
    rw [dist_comm x o] at h
    linarith
  · linarith [dist_triangle o x (ray j)]

theorem signedDistanceSequence_sub_abs_le (o : E) (ray : ℝ≥0 → E)
    (x y : E) (j : ℕ) :
    |signedDistanceSequence o ray x j - signedDistanceSequence o ray y j| ≤ dist x y := by
  dsimp [signedDistanceSequence]
  apply abs_le.mpr
  have hxy := dist_triangle x y (ray j)
  have hyx := dist_triangle y x (ray j)
  rw [dist_comm y x] at hyx
  constructor <;> linarith

theorem dist_origin_ray (o : E) (ray : ℝ≥0 → E) (hzero : ray 0 = o)
    (hray : ∀ s t, dist (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|) (j : ℕ) :
    dist o (ray j) = (j : ℝ) := by
  simpa only [hzero, NNReal.coe_zero, NNReal.coe_natCast, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j)] using hray 0 (j : ℝ≥0)

theorem signedDistanceSequence_monotone (o : E) (ray : ℝ≥0 → E)
    (hzero : ray 0 = o)
    (hray : ∀ s t, dist (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|) (x : E) :
    Monotone (signedDistanceSequence o ray x) := by
  intro j k hjk
  have htri := dist_triangle x (ray j) (ray k)
  rw [hray, NNReal.coe_natCast, NNReal.coe_natCast,
    abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hjk))] at htri
  dsimp [signedDistanceSequence]
  rw [dist_origin_ray o ray hzero hray j, dist_origin_ray o ray hzero hray k]
  linarith

def busemannValue (o : E) (ray : ℝ≥0 → E) (x : E) : ℝ :=
  sSup (Set.range (signedDistanceSequence o ray x))

theorem tendsto_busemannValue (o : E) (ray : ℝ≥0 → E)
    (hzero : ray 0 = o)
    (hray : ∀ s t, dist (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|) (x : E) :
    Tendsto (signedDistanceSequence o ray x) atTop (𝓝 (busemannValue o ray x)) := by
  have hbounded : BddAbove (Set.range (signedDistanceSequence o ray x)) := by
    refine ⟨dist o x, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact (signedDistanceSequence_bounds o ray x j).2
  exact tendsto_atTop_isLUB (signedDistanceSequence_monotone o ray hzero hray x)
    (isLUB_csSup (Set.range_nonempty _) hbounded)

theorem busemannValue_lipschitz (o : E) (ray : ℝ≥0 → E)
    (hzero : ray 0 = o)
    (hray : ∀ s t, dist (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|) (x y : E) :
    |busemannValue o ray x - busemannValue o ray y| ≤ dist x y := by
  apply le_of_tendsto'
    (((tendsto_busemannValue o ray hzero hray x).sub
      (tendsto_busemannValue o ray hzero hray y)).abs)
  exact fun j => signedDistanceSequence_sub_abs_le o ray x y j

theorem exists_busemann_limit (o : E) (ray : ℝ≥0 → E)
    (hzero : ray 0 = o)
    (hray : ∀ s t, dist (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|) :
    ∃ b : E → ℝ,
      (∀ x, Tendsto (fun j : ℕ => dist o (ray j) - dist x (ray j)) atTop (𝓝 (b x))) ∧
      (∀ x y, |b x - b y| ≤ dist x y) :=
  ⟨busemannValue o ray, tendsto_busemannValue o ray hzero hray,
    busemannValue_lipschitz o ray hzero hray⟩

end Yau.NodeProofs.P01Aux
