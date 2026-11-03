import Yau.Proofs.V03ContinuousMapDerivative

/-! Actual uniform-norm regularity follows from pointwise derivatives
and regular derivative traces on an open parameter set. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {K P F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_continuousMap_on_open {U : Set P} (hU : IsOpen U)
    {u : P → C(K, F)} {A : P → C(K, P →L[ℝ] F)}
    (hA : ContinuousOn A U)
    (hd : ∀ y ∈ U, ∀ k, HasFDerivAt (fun x => u x k) (A y k) y)
    {p : P} (hp : p ∈ U) : HasFDerivAt u (continuousMapOperator (A p)) p := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  exact hasFDerivAt_continuousMap_of_pointwise hr (hA.continuousAt (hU.mem_nhds hp))
    (fun y hy k => hd y (hsub hy) k)

theorem contDiffOn_continuousMap_succ {U : Set P} (hU : IsOpen U)
    {u : P → C(K, F)} {A : P → C(K, P →L[ℝ] F)} (m : ℕ)
    (hA : ContDiffOn ℝ m A U)
    (hd : ∀ y ∈ U, ∀ k, HasFDerivAt (fun x => u x k) (A y k) y) :
    ContDiffOn ℝ (m + 1) u U := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
  refine ⟨by simp, (fun y => continuousMapOperator (A y)), ?_, ?_⟩
  · exact continuousMapOperatorL.contDiff.comp_contDiffOn hA
  · intro p hp
    exact (hasFDerivAt_continuousMap_on_open hU hA.continuousOn hd hp).hasFDerivWithinAt

theorem contDiffOn_continuousMap_infty {U : Set P} (hU : IsOpen U)
    {u : P → C(K, F)} {A : P → C(K, P →L[ℝ] F)}
    (hA : ContDiffOn ℝ ∞ A U)
    (hd : ∀ y ∈ U, ∀ k, HasFDerivAt (fun x => u x k) (A y k) y) :
    ContDiffOn ℝ ∞ u U := by
  have hD (p : P) (hp : p ∈ U) : HasFDerivAt u (continuousMapOperator (A p)) p :=
    hasFDerivAt_continuousMap_on_open hU hA.continuousOn hd hp
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hU]
  refine ⟨fun p hp => (hD p hp).differentiableAt.differentiableWithinAt, ?_⟩
  have hB : ContDiffOn ℝ ∞ (fun y => continuousMapOperator (A y)) U := by
    simpa only [Function.comp_def, continuousMapOperatorL_apply] using
      (continuousMapOperatorL (𝕜 := ℝ) (K := K) (P := P) (F := F)).contDiff.comp_contDiffOn hA
  exact hB.congr (fun p hp => (hD p hp).fderiv)

end Yau.Blueprint.V03Proof
