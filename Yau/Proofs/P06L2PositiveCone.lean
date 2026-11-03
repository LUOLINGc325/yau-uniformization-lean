import Yau.Proofs.P06PositiveResidual

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual L² positive (1,1) cone, tested against all original positive
L² forms; its type condition is the genuine orthogonal projection. -/
def hodgeL2PositiveCone (g : SmoothMetric M) (μ : Measure M.Carrier) : Set (L2FormHilbert g μ 2) :=
  {f | oneOneProjectionHilbert g μ f = f ∧
    ∀ (B : RealForm M 2) (hB : L2RealForm g.form μ B), RealOneOne B → FormLE 0 B →
      0 ≤ inner ℝ f (realizeActualForm g μ B hB)}

theorem hodgeL2PositiveCone_isClosed (g : SmoothMetric M) (μ : Measure M.Carrier) :
    IsClosed (hodgeL2PositiveCone g μ) := by
  simp only [hodgeL2PositiveCone, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter (isClosed_eq (oneOneProjectionHilbert g μ).continuous continuous_id)
  refine isClosed_iInter (fun B => isClosed_iInter (fun hB => isClosed_iInter (fun _ =>
    isClosed_iInter (fun _ => ?_))))
  exact isClosed_le continuous_const (continuous_id.inner continuous_const)

theorem hodgeL2PositiveCone_convex (g : SmoothMetric M) (μ : Measure M.Carrier) :
    Convex ℝ (hodgeL2PositiveCone g μ) := by
  intro f hf k hk a b ha hb hab
  constructor
  · simp only [map_add, map_smul, hf.1, hk.1]
  · intro B hB h11 hp
    simp only [inner_add_left, inner_smul_left, conj_trivial]
    exact add_nonneg (mul_nonneg ha (hf.2 B hB h11 hp)) (mul_nonneg hb (hk.2 B hB h11 hp))

theorem realizeActualForm_mem_hodgeL2PositiveCone (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) (hp : FormLE 0 A) :
    realizeActualForm g μ A hA ∈ hodgeL2PositiveCone g μ := by
  constructor
  · rw [oneOneProjectionHilbert_realize]
    apply realizeActualForm_congr
    exact P06Weitzenbock.oneOneProjection_fixed A h11
  · intro B hB h11B hpB
    rw [realizeActualForm_inner]
    exact integral_nonneg (fun x => formInner_nonnegative_oneOne g.form A B h11 h11B hp hpB x)

theorem positiveForm_Hilbert_normal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (f : L2FormHilbert g μ 2) (hf : f ∈ hodgeL2PositiveCone g μ) :
    inner ℝ (realizeActualForm g μ A hA - realizeActualForm g μ (Clip.positiveForm g.form A)
      (FiberApprox.positiveForm_l2_of_l2 g μ A hA h11))
      (f - realizeActualForm g μ (Clip.positiveForm g.form A)
        (FiberApprox.positiveForm_l2_of_l2 g μ A hA h11)) ≤ 0 := by
  let P := Clip.positiveForm g.form A
  let N := Clip.positiveForm g.form (-A)
  have hneg : L2RealForm g.form μ (-A) := by
    simpa only [zero_sub] using l2RealForm_sub g μ 0 A (l2RealForm_zero g.form μ) hA
  have hP : L2RealForm g.form μ P := FiberApprox.positiveForm_l2_of_l2 g μ A hA h11
  have hN : L2RealForm g.form μ N :=
    FiberApprox.positiveForm_l2_of_l2 g μ (-A) hneg (Clip.realOneOne_neg A h11)
  let p := realizeActualForm g μ P hP
  let q := realizeActualForm g μ N hN
  have hsplit : realizeActualForm g μ A hA = p - q := by
    calc
      _ = realizeActualForm g μ (P - N) (l2RealForm_sub g μ P N hP hN) :=
        realizeActualForm_congr g μ A (P - N) hA _ (Clip.positiveForm_split g.form A h11)
      _ = _ := realizeActualForm_sub g μ P N hP hN
  have horth : inner ℝ q p = 0 := by
    rw [real_inner_comm]
    change inner ℝ (realizeActualForm g μ P hP) (realizeActualForm g μ N hN) = 0
    simp only [realizeActualForm_inner, P, N, Clip.formInner_positive_neg_zero, integral_zero]
  have htest : 0 ≤ inner ℝ f q := hf.2 N hN (Clip.positiveForm_oneOne g.form (-A))
    (Clip.positiveForm_nonnegative g.form (-A))
  change inner ℝ (realizeActualForm g μ A hA - p) (f - p) ≤ 0
  rw [hsplit]
  have he : (p - q) - p = -q := by abel
  rw [he, inner_neg_left, inner_sub_right, horth, sub_zero, real_inner_comm f q]
  exact neg_nonpos.mpr htest

end Yau.NodeProofs.P06Aux
