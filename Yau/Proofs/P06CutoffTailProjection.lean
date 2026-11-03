import Yau.Proofs.P06HodgeDavies
import Yau.Proofs.P06CutoffTailSeries

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.CutoffTail
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Davies
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem indicator_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s) (u : L2FormHilbert g μ k) :
    ‖indicator g μ s hs u‖ ≤ ‖u‖ := by
  simpa only [one_mul, Davies.indicator] using multiplyL2FormHilbert_norm_le g μ
    (s.indicator (fun _ => (1 : ℝ)))
    (stronglyMeasurable_const.indicator hs).aestronglyMeasurable
    1 zero_le_one (fun x => by by_cases hx : x ∈ s <;> simp [hx]) u

theorem indicator_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s) (u v : L2FormHilbert g μ k) :
    inner ℝ (indicator g μ s hs u) v = inner ℝ u (indicator g μ s hs v) :=
  multiplyL2FormHilbert_inner_symm g μ _ _ _ _ _ u v

theorem indicator_inter (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s t : Set M.Carrier) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (u : L2FormHilbert g μ k) :
    indicator g μ s hs (indicator g μ t ht u) =
      indicator g μ (s ∩ t) (hs.inter ht) u := by
  apply multiplier_comp_eq g μ _ _ _ _ _ _ 1 1 1 zero_le_one zero_le_one zero_le_one
    (fun x => by by_cases hx : x ∈ s <;> simp [hx])
    (fun x => by by_cases hx : x ∈ t <;> simp [hx])
    (fun x => by by_cases hx : x ∈ s ∩ t <;> simp [hx])
    (fun x => by by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy]) u

theorem indicator_idem (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s) (u : L2FormHilbert g μ k) :
    indicator g μ s hs (indicator g μ s hs u) = indicator g μ s hs u := by
  simpa only [Set.inter_self] using indicator_inter g μ s s hs hs u

theorem indicator_norm_mono (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s t : Set M.Carrier) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (u : L2FormHilbert g μ k) :
    ‖indicator g μ s hs u‖ ≤ ‖indicator g μ t ht u‖ := by
  have he : indicator g μ s hs (indicator g μ t ht u) = indicator g μ s hs u := by
    simpa only [Set.inter_eq_left.mpr hst] using indicator_inter g μ s t hs ht u
  rw [← he]
  exact indicator_norm_le g μ s hs _

theorem indicator_diff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s t : Set M.Carrier) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (u : L2FormHilbert g μ k) :
    indicator g μ (t \ s) (ht.diff hs) u = indicator g μ t ht u - indicator g μ s hs u := by
  refine UniformSpace.Completion.induction_on u
    (p := fun u => indicator g μ (t \ s) (ht.diff hs) u =
      indicator g μ t ht u - indicator g μ s hs u) ?_ ?_
  · exact isClosed_eq (indicator g μ (t \ s) (ht.diff hs)).continuous
      ((indicator g μ t ht).continuous.sub (indicator g μ s hs).continuous)
  · intro v
    change indicator g μ (t \ s) (ht.diff hs) (realizeL2Form g μ v) =
      indicator g μ t ht (realizeL2Form g μ v) - indicator g μ s hs (realizeL2Form g μ v)
    simp only [indicator, multiplyL2FormHilbert_realize]
    rw [← realizeL2Form_sub]
    congr 1
    apply L2FormSpace.toSection_injective g μ k
    funext x
    simp only [multiplyL2FormLinear_toSection, L2FormSpace.toSection_sub,
      multiplyRealForm, Pi.sub_apply]
    by_cases hx : x ∈ s
    · simp [hx, hst hx]
    · by_cases hy : x ∈ t <;> simp [hx, hy]

/-- Self-adjointness converts the proved outward Davies estimate to the
inward estimate needed for cutoff tails, in the same original Hilbert space. -/
theorem reverse_annular_tail (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (A : ℝ) (hA : 1 ≤ A)
    (htail : ∀ (r R : ℝ), 0 < r → r < R → ∀ t, 0 < t →
      ∀ f : L2FormHilbert g μ k,
      indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) f = f →
      ‖indicator g μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (hodgeHeatHilbert g μ hμ k t f)‖ ≤
        Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖)
    (r R t : ℝ) (hr : 0 < r) (hrR : r < R) (ht : 0 < t)
    (f : L2FormHilbert g μ k)
    (hf : indicator g μ (distBall g.form o R)ᶜ
      (L12Aux.measurableSet_distBall g o R).compl f = f) :
    ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
      (hodgeHeatHilbert g μ hμ k t f)‖ ≤
      Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖ := by
  let P := indicator (k := k) g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
  let Q := indicator (k := k) g μ (distBall g.form o R)ᶜ (L12Aux.measurableSet_distBall g o R).compl
  let S := hodgeHeatHilbert g μ hμ k t
  let u := P (S f)
  have hu : P u = u := indicator_idem g μ _ _ (S f)
  have hq : Q f = f := hf
  have hsym := hodgeHeatHilbert_symmetric g μ hμ k t
  have he : inner ℝ u u = inner ℝ (Q (S u)) f := by
    calc
      _ = inner ℝ (S f) (P u) := indicator_symmetric g μ _ _ (S f) u
      _ = inner ℝ f (S u) := by rw [hu]; exact hsym f u
      _ = inner ℝ (Q f) (S u) := by rw [hq]
      _ = inner ℝ f (Q (S u)) := indicator_symmetric g μ _ _ f (S u)
      _ = _ := real_inner_comm _ _
  have hb := htail r R hr hrR t ht u hu
  change ‖Q (S u)‖ ≤ _ at hb
  have hh : ‖u‖ ^ 2 ≤
      (Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖) * ‖u‖ := by
    calc
      _ = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
      _ = inner ℝ (Q (S u)) f := he
      _ ≤ ‖Q (S u)‖ * ‖f‖ := real_inner_le_norm _ _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg f)]
  change ‖u‖ ≤ _
  by_cases hz : u = 0
  · simp only [hz, norm_zero]
    positivity
  · apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)).mp
    nlinarith only [hh]

end Yau.NodeProofs.P06Aux.CutoffTail
