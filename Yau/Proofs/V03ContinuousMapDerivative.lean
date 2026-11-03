import Yau.Proofs.V03ContinuousMapOperator
import Mathlib.Analysis.Calculus.MeanValue

/-! Pointwise genuine derivatives with continuous compact-trace derivative
data give a genuine derivative in the uniform norm. The proof is a uniform
mean-value remainder estimate. -/

open scoped Topology
open Filter Asymptotics

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {K P F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_continuousMap_of_pointwise {u : P → C(K, F)}
    {A : P → C(K, P →L[ℝ] F)} {p : P} {r : ℝ} (hr : 0 < r)
    (hA : ContinuousAt A p)
    (hd : ∀ y ∈ Metric.ball p r, ∀ k, HasFDerivAt (fun x => u x k) (A y k) y) :
    HasFDerivAt u (continuousMapOperator (A p)) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hnear : ∀ᶠ y in 𝓝 p, ‖A y - A p‖ < ε := by
    have hh := hA.eventually (Metric.ball_mem_nhds (A p) hε)
    filter_upwards [hh] with y hy
    change dist (A y) (A p) < ε at hy
    have hd : dist (A y) (A p) = ‖A y - A p‖ :=
      @dist_eq_norm C(K, P →L[ℝ] F) inferInstance (A y) (A p)
    rwa [hd] at hy
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let R := min r δ
  have hR : 0 < R := lt_min hr hδ
  filter_upwards [Metric.ball_mem_nhds (0 : P) hR] with v hv
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro k
  have hder (x : P) (hx : x ∈ Metric.ball p R) :
      HasFDerivWithinAt (fun y => u y k - A p k y) (A x k - A p k) (Metric.ball p R) x := by
    exact ((hd x (Metric.ball_subset_ball (min_le_left r δ) hx) k).sub
      (A p k).hasFDerivAt).hasFDerivWithinAt
  have hbound (x : P) (hx : x ∈ Metric.ball p R) : ‖A x k - A p k‖ ≤ ε := by
    have hxs : x ∈ Metric.ball p δ := Metric.ball_subset_ball (min_le_right r δ) hx
    have hsmall : ‖A x - A p‖ < ε := hδsub hxs
    exact ((A x - A p).norm_coe_le_norm k).trans hsmall.le
  have hpR : p ∈ Metric.ball p R := by simpa using hR
  have hpvR : p + v ∈ Metric.ball p R := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hvR
  have hm := (convex_ball p R).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hder hbound hpR hpvR
  have heq : (u (p + v) k - A p k (p + v)) - (u p k - A p k p) =
      u (p + v) k - u p k - A p k v := by rw [map_add]; abel
  rw [heq, add_sub_cancel_left] at hm
  exact hm

end Yau.Blueprint.V03Proof
