import Yau.Proofs.P06CutoffTailAnnuli
import Yau.Proofs.P06CutoffData

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.CutoffTail
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03 Davies
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Only the unused zeroth cutoff is normalized; every positive index is
literally the originally supplied cutoff. -/
def cutoffScalar (χ : ℕ → M.Carrier → ℝ) (j : ℕ) : M.Carrier → ℝ :=
  if 1 ≤ j then χ j else 0

def cutoffForm (χ : ℕ → M.Carrier → ℝ) (A : RealForm M k) (j : ℕ) : RealForm M k :=
  multiplyRealForm (cutoffScalar χ j) A

theorem cutoffScalar_smooth (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ) (j : ℕ) :
    SmoothFn (cutoffScalar χ j) := by
  obtain ⟨C, hC, hc⟩ := hχ
  by_cases hj : 1 ≤ j
  · simpa only [cutoffScalar, ite_eq_left hj] using (hc j hj).1
  · simp only [cutoffScalar, ite_eq_right hj]
    exact fun x => contDiffOn_const

theorem cutoffScalar_compact (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ) (j : ℕ) :
    HasCompactSupport (cutoffScalar χ j) := by
  obtain ⟨C, hC, hc⟩ := hχ
  by_cases hj : 1 ≤ j
  · simpa only [cutoffScalar, ite_eq_left hj] using (hc j hj).2.1
  · simp only [cutoffScalar, ite_eq_right hj]
    exact HasCompactSupport.zero

theorem cutoffScalar_range (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ) (j : ℕ) (x : M.Carrier) :
    cutoffScalar χ j x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨C, hC, hc⟩ := hχ
  by_cases hj : 1 ≤ j
  · simpa only [cutoffScalar, ite_eq_left hj, Set.mem_Icc] using (hc j hj).2.2.1 x
  · simp [cutoffScalar, hj]

theorem cutoffForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (j : ℕ) :
    L2RealForm g.form μ (cutoffForm χ A j) :=
  smooth_compactlySupported_l2RealForm g μ hμ _
    (smoothRealForm_multiply _ A (cutoffScalar_smooth g o χ hχ j) hA)
    (compactlySupportedRealForm_multiply_scalar _ (cutoffScalar_compact g o χ hχ j) A)

def cutoffDatum (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (j : ℕ) : L2FormHilbert g μ k :=
  realizeActualForm g μ (cutoffForm χ A j) (cutoffForm_l2 g μ hμ o χ hχ A hA j)

theorem cutoffDatum_eq_actual (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (j : ℕ) (hj : 1 ≤ j) :
    cutoffDatum g μ hμ o χ hχ A hA j =
      realizeActualForm g μ (fun x => χ j x • A x)
        (metricCutoff_smooth_l2 g μ hμ o χ hχ A hA j hj) := by
  simp only [cutoffDatum, cutoffForm, cutoffScalar, ite_eq_left hj]
  rfl

theorem cutoffForm_compact (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (j : ℕ) : CompactlySupportedRealForm (cutoffForm χ A j) :=
  compactlySupportedRealForm_multiply_scalar _ (cutoffScalar_compact g o χ hχ j) A

theorem compactlySupported_sub (A D : RealForm M k)
    (hA : CompactlySupportedRealForm A) (hD : CompactlySupportedRealForm D) :
    CompactlySupportedRealForm (A - D) := by
  apply (hA.union hD).of_isClosed_subset isClosed_closure
  rw [← closure_union]
  apply closure_mono
  intro x hx
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  exact hx (by simp only [Pi.sub_apply, h.1, h.2, sub_self])

/-- The difference of two arbitrary admissible cutoffs has the original
pointwise form bound, uniformly in both indices and basepoints. -/
theorem cutoff_difference_bound (g : SmoothMetric M)
    (o o' : M.Carrier) (χ χ' : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ) (hχ' : MetricCutoffFamily g.form o' χ')
    (A : RealForm M k) (B : ℝ) (hb : ∀ x, formNormSq g.form A x ≤ B ^ 2)
    (j l : ℕ) (x : M.Carrier) :
    formNormSq g.form (cutoffForm χ A j - cutoffForm χ' A l) x ≤ B ^ 2 := by
  have he : cutoffForm χ A j - cutoffForm χ' A l =
      multiplyRealForm (fun y => cutoffScalar χ j y - cutoffScalar χ' l y) A := by
    funext y
    exact (sub_smul _ _ _).symm
  rw [he, multiplyRealForm_normSq]
  obtain ⟨h₁0, h₁1⟩ := cutoffScalar_range g o χ hχ j x
  obtain ⟨h₂0, h₂1⟩ := cutoffScalar_range g o' χ' hχ' l x
  have hs : (cutoffScalar χ j x - cutoffScalar χ' l x) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (cutoffScalar χ j x - cutoffScalar χ' l x + 1),
      mul_nonneg (by linarith : 0 ≤ 1 - (cutoffScalar χ j x - cutoffScalar χ' l x))
        (by linarith : 0 ≤ 1 + (cutoffScalar χ j x - cutoffScalar χ' l x))]
  exact (mul_le_of_le_one_left (formNormSq_nonneg g.form A x) hs).trans (hb x)

/-- Both basepoints are allowed to vary.  The fixed test ball is covered
by each original family after one index, uniformly over the ball. -/
theorem cutoffScalar_eventually_one_on_ball (g : SmoothMetric M)
    (o p : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (R : ℝ) (hR : 0 < R) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j, N ≤ j → ∀ x ∈ distBall g.form p R,
      cutoffScalar χ j x = 1 := by
  obtain ⟨C, hC, hc⟩ := hχ
  obtain ⟨N, hN⟩ := exists_nat_gt (inducedDistance g.form o p + R)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro j hj x hx
  have hj1 := (le_max_right N 1).trans hj
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  simp only [cutoffScalar, ite_eq_left hj1]
  apply (hc j hj1).2.2.2.1 x
  apply (L12Aux.mem_distBall_iff g o x hjpos).mpr
  calc
    inducedDistance g.form o x ≤ inducedDistance g.form o p + inducedDistance g.form p x :=
      g.induced_distance_triangle o p x
    _ < inducedDistance g.form o p + R := by
      have := (L12Aux.mem_distBall_iff g p x hR).mp hx
      linarith
    _ < (N : ℝ) := hN
    _ ≤ j := by exact_mod_cast (le_max_left N 1).trans hj

theorem indicator_realize_zero_on (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (hz : ∀ x ∈ s, A x = 0) :
    indicator g μ s hs (realizeActualForm g μ A hA) = 0 := by
  apply norm_eq_zero.mp
  have hh := indicator_realize_norm_sq g μ s hs A hA
  have hi : (∫ x in s, formNormSq g.form A x ∂μ) = 0 := by
    calc
      _ = ∫ x in s, (0 : ℝ) ∂μ := setIntegral_congr_fun hs (fun x hx => by
        exact (formNormSq_eq_zero_iff g.form A x).mpr (hz x hx))
      _ = 0 := by simp
  rw [hi] at hh
  nlinarith [norm_nonneg (indicator g μ s hs (realizeActualForm g μ A hA))]

end Yau.NodeProofs.P06Aux.CutoffTail
