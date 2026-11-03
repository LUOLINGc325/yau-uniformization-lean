import Yau.Proofs.P06L2IntervalCone

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem metricCutoff_realize_shift_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (B : RealForm M 2) (hB : L2RealForm g.form μ B)
    (hBj : ∀ j, L2RealForm g.form μ (multiplyRealForm (χ (j + 1)) B)) :
    Tendsto (fun j => realizeActualForm g μ (multiplyRealForm (χ (j + 1)) B) (hBj j)) atTop
      (𝓝 (realizeActualForm g μ B hB)) := by
  have hd := (metricCutoff_l2_distance_tendsto g μ o χ hχ B hB).comp (tendsto_add_atTop_nat 1)
  apply (tendsto_realizeL2Form_iff g μ
    (fun j => L2FormSpace.ofSection (multiplyRealForm (χ (j + 1)) B) (hBj j))
    (L2FormSpace.ofSection B hB)).mpr
  change Tendsto (fun j => formL2DistanceSq g.form μ (fun x => χ (j + 1) x • B x) B) atTop (𝓝 0)
  exact hd

/-- The exact interval projection normal inequality is obtained from
compact positive tests of its two L² residuals. Cutoff removal is in L²;
no global L¹ trace of either residual is assumed, even when C=0. -/
theorem intervalForm_Hilbert_normal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) {C : ℝ} (hC : 0 ≤ C)
    (f : L2FormHilbert g μ 2) (hf : f ∈ hodgeL2IntervalCone g μ C) :
    inner ℝ (realizeActualForm g μ A hA - realizeActualForm g μ (Clip.intervalForm g.form C A)
      (FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC))
      (f - realizeActualForm g μ (Clip.intervalForm g.form C A)
        (FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC)) ≤ 0 := by
  classical
  let P := Clip.intervalForm g.form C A
  let U := Clip.intervalUpperForm g.form C A
  let L := Clip.intervalLowerForm g.form C A
  have hP : L2RealForm g.form μ P := FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC
  have hU : L2RealForm g.form μ U := Clip.intervalUpperForm_l2 g μ A hA h11 hC
  have hL : L2RealForm g.form μ L := Clip.intervalLowerForm_l2 g μ A hA h11 hC
  let p := realizeActualForm g μ P hP
  let u := realizeActualForm g μ U hU
  let l := realizeActualForm g μ L hL
  have hsplit : realizeActualForm g μ A hA - p = u - l := by
    calc
      _ = realizeActualForm g μ (A - P) (l2RealForm_sub g μ A P hA hP) :=
        (realizeActualForm_sub g μ A P hA hP).symm
      _ = realizeActualForm g μ (U - L) (l2RealForm_sub g μ U L hU hL) :=
        realizeActualForm_congr g μ (A - P) (U - L) _ _ (Clip.intervalForm_residual_split g.form C A h11)
      _ = _ := realizeActualForm_sub g μ U L hU hL
  let o : M.Carrier := Classical.choice inferInstance
  obtain ⟨χ, hχ⟩ := metricCutoffFamily g o
  obtain ⟨D, hD, hc⟩ := hχ
  have hfamily : MetricCutoffFamily g.form o χ := ⟨D, hD, hc⟩
  let η (j : ℕ) := χ (j + 1)
  have hη (j : ℕ) : SmoothFn (η j) := (hc (j + 1) (by omega)).1
  have hcη (j : ℕ) : HasCompactSupport (η j) := (hc (j + 1) (by omega)).2.1
  have hηp (j : ℕ) (x : M.Carrier) : 0 ≤ η j x := ((hc (j + 1) (by omega)).2.2.1 x).1
  have hUj (j : ℕ) : L2RealForm g.form μ (multiplyRealForm (η j) U) :=
    l2RealForm_multiply_smooth_compact g μ _ (hη j) (hcη j) U hU
  have hLj (j : ℕ) : L2RealForm g.form μ (multiplyRealForm (η j) L) :=
    l2RealForm_multiply_smooth_compact g μ _ (hη j) (hcη j) L hL
  have hupper (j : ℕ) : inner ℝ (f - p) (realizeActualForm g μ (multiplyRealForm (η j) U) (hUj j)) ≤ 0 := by
    have ht := hf.2 (multiplyRealForm (η j) U) (hUj j)
      (realOneOne_multiply (η j) U (Clip.intervalUpperForm_oneOne g.form C A))
      (formLE_multiply_nonnegative g.form _ (hηp j) U (Clip.intervalUpperForm_nonnegative g.form C A))
      (TraceHilbert.compact_trace_integrable g μ hμ U hU (Clip.intervalUpperForm_oneOne g.form C A) _ (hη j) (hcη j))
    have hp := contact_cutoff_pairing g μ P U hP hU (Clip.intervalUpperForm_oneOne g.form C A) C
      (fun x => by
        rw [congrFun (formInner_symm g.form P U) x]
        exact Clip.formInner_intervalUpper g.form hC A h11 x)
      _ (hη j) (hcη j)
    rw [inner_sub_left]
    have hu := (le_abs_self (inner ℝ f (realizeActualForm g μ (multiplyRealForm (η j) U) (hUj j)))).trans ht
    change inner ℝ f _ - inner ℝ (realizeActualForm g μ P hP) _ ≤ 0
    linarith
  have hlower (j : ℕ) : 0 ≤ inner ℝ (f - p) (realizeActualForm g μ (multiplyRealForm (η j) L) (hLj j)) := by
    have ht := hf.2 (multiplyRealForm (η j) L) (hLj j)
      (realOneOne_multiply (η j) L (Clip.intervalLowerForm_oneOne g.form C A))
      (formLE_multiply_nonnegative g.form _ (hηp j) L (Clip.intervalLowerForm_nonnegative g.form C A))
      (TraceHilbert.compact_trace_integrable g μ hμ L hL (Clip.intervalLowerForm_oneOne g.form C A) _ (hη j) (hcη j))
    have hp := contact_cutoff_pairing g μ P L hP hL (Clip.intervalLowerForm_oneOne g.form C A) (-C)
      (fun x => by
        rw [congrFun (formInner_symm g.form P L) x]
        exact Clip.formInner_intervalLower g.form hC A h11 x)
      _ (hη j) (hcη j)
    have hlo := (abs_le.mp ht).1
    rw [inner_sub_left]
    change 0 ≤ inner ℝ f _ - inner ℝ (realizeActualForm g μ P hP) _
    linarith
  have hUt := metricCutoff_realize_shift_tendsto g μ o χ hfamily U hU hUj
  have hLt := metricCutoff_realize_shift_tendsto g μ o χ hfamily L hL hLj
  have hcont : Continuous (fun z : L2FormHilbert g μ 2 => inner ℝ (f - p) z) :=
    continuous_const.inner continuous_id
  have hUinner : Tendsto (fun j => inner ℝ (f - p)
      (realizeActualForm g μ (multiplyRealForm (η j) U) (hUj j))) atTop (𝓝 (inner ℝ (f - p) u)) := by
    simpa only [Function.comp_def] using hcont.continuousAt.tendsto.comp hUt
  have hLinner : Tendsto (fun j => inner ℝ (f - p)
      (realizeActualForm g μ (multiplyRealForm (η j) L) (hLj j))) atTop (𝓝 (inner ℝ (f - p) l)) := by
    simpa only [Function.comp_def] using hcont.continuousAt.tendsto.comp hLt
  have hUi : inner ℝ (f - p) u ≤ 0 := isClosed_Iic.mem_of_tendsto hUinner (Eventually.of_forall hupper)
  have hLi : 0 ≤ inner ℝ (f - p) l := isClosed_Ici.mem_of_tendsto hLinner (Eventually.of_forall hlower)
  change inner ℝ (realizeActualForm g μ A hA - p) (f - p) ≤ 0
  rw [hsplit, inner_sub_left, real_inner_comm (f - p) u, real_inner_comm (f - p) l]
  linarith

end Yau.NodeProofs.P06Aux
