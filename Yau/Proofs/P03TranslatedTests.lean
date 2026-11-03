import Yau.Proofs.P03Convolution
import Yau.Proofs.P03Measure

open scoped Topology ContDiff
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

theorem translatedKernel_contDiff {k : ComplexVector n → ℂ}
    (hk : ContDiff ℝ ∞ k) (x : ComplexVector n) :
    ContDiff ℝ ∞ (fun y => k (x - y)) :=
  hk.comp (contDiff_const.sub contDiff_id)

theorem translatedKernel_hasCompactSupport {k : ComplexVector n → ℂ}
    (hkc : HasCompactSupport k) (x : ComplexVector n) :
    HasCompactSupport (fun y => k (x - y)) :=
  hkc.comp_homeomorph (Homeomorph.subLeft x)

theorem translatedKernel_tsupport {k : ComplexVector n → ℂ} {r : ℝ}
    (hks : tsupport k ⊆ Metric.closedBall 0 r) (x : ComplexVector n) :
    tsupport (fun y => k (x - y)) ⊆ Metric.closedBall x r := by
  have he := tsupport_comp_eq_preimage k (Homeomorph.subLeft x)
  rw [show (fun y => k (x - y)) = k ∘ Homeomorph.subLeft x from rfl, he]
  intro y hy
  have h := hks hy
  simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using h

theorem wirtBar_translatedKernel {k : ComplexVector n → ℂ}
    (hk : ContDiff ℝ ∞ k) (x y v : ComplexVector n) :
    wirtBar (fun t => k (x - t)) y v = -wirtBar k (x - y) v := by
  have hd := ((hk.differentiable (by simp)) (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub x)
  have he : fderiv ℝ (fun t => k (x - t)) y =
      (fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ (ComplexVector n)) := by
    convert! hd.fderiv using 1
  unfold wirtBar
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg]
  ring

theorem wirtBar_zero_of_notMem_tsupport {ψ : ComplexVector n → ℂ}
    {y : ComplexVector n} (hy : y ∉ tsupport ψ) (v : ComplexVector n) :
    wirtBar ψ y v = 0 := by
  unfold wirtBar
  rw [fderiv_of_notMem_tsupport ℝ hy]
  simp

theorem indicator_mul_wirtBar_eq_of_tsupport_subset {u ψ : ComplexVector n → ℂ}
    {K : Set (ComplexVector n)} (hs : tsupport ψ ⊆ K) (y v : ComplexVector n) :
    K.indicator u y * wirtBar ψ y v = u y * wirtBar ψ y v := by
  classical
  by_cases hy : y ∈ K
  · simp only [Set.indicator_of_mem hy]
  · have hout : y ∉ tsupport ψ := fun h => hy (hs h)
    simp [Set.indicator_of_notMem hy, wirtBar_zero_of_notMem_tsupport hout v]

theorem translatedKernel_inner_support {k : ComplexVector n → ℂ} {r : ℝ}
    (hks : tsupport k ⊆ Metric.closedBall 0 r) {a x : ComplexVector n}
    (hx : x ∈ Metric.ball a (3 * r)) :
    tsupport (fun y => k (x - y)) ⊆ Metric.closedBall a (4 * r) := by
  intro y hy
  have hxy := translatedKernel_tsupport hks x hy
  have h1 : dist y x ≤ r := Metric.mem_closedBall.mp hxy
  have h2 : dist x a < 3 * r := Metric.mem_ball.mp hx
  apply Metric.mem_closedBall.mpr
  calc
    dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
    _ ≤ r + 3 * r := add_le_add h1 h2.le
    _ = 4 * r := by ring

end Yau.NodeProofs.P03Aux
