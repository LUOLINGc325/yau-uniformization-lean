import Yau.LeafProofs.L17UniformCover

/-! Actual compact smooth weights transported by the original holomorphic charts. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

def chartExtensionZero {F : Type*} [Zero F]
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (φ : ComplexVector n → F) (y : M.Carrier) : F := by
  classical
  exact if y ∈ e.target then φ (e.symm y) else 0

theorem chartExtensionZero_properties
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {φ : ComplexVector n → F} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hsource : tsupport φ ⊆ e.source) :
    HasCompactSupport (chartExtensionZero e φ) ∧
      ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞ (chartExtensionZero e φ) ∧
      tsupport (chartExtensionZero e φ) ⊆ e '' tsupport φ := by
  let := L12Aux.manifold_realSmooth M
  let Ξ := chartExtensionZero e φ
  let K := e '' tsupport φ
  have hK : IsCompact K := hcφ.image_of_continuousOn (e.continuousOn.mono hsource)
  have hKt : K ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hsource hz)
  have hsupp : Function.support Ξ ⊆ K := by
    intro y hy
    change Ξ y ≠ 0 at hy
    by_cases hyt : y ∈ e.target
    · have hnz : φ (e.symm y) ≠ 0 := by
        simpa only [Ξ, chartExtensionZero, ite_eq_left hyt] using hy
      exact ⟨e.symm y, subset_closure hnz, e.right_inv hyt⟩
    · exact False.elim (hy (by simp only [Ξ, chartExtensionZero, ite_eq_right hyt]))
  have htsupp : tsupport Ξ ⊆ K := closure_minimal hsupp hK.isClosed
  have hcΞ : HasCompactSupport Ξ := hK.of_isClosed_subset (isClosed_tsupport Ξ) htsupp
  refine ⟨hcΞ, ?_, htsupp⟩
  apply contMDiff_of_tsupport
  intro y hy
  have hyt := hKt (htsupp hy)
  have hi := ((inverse_chart_real_contMDiffOn e hei) y hyt).contMDiffAt
    (e.open_target.mem_nhds hyt)
  have hcomp := hφ.contMDiff.contMDiffAt.comp y hi
  have heq : Ξ =ᶠ[𝓝 y] (φ ∘ e.symm) := by
    filter_upwards [e.open_target.mem_nhds hyt] with z hz
    simp only [Ξ, chartExtensionZero, ite_eq_left hz, Function.comp_apply]
  exact hcomp.congr_of_eventuallyEq heq

def innerChartBump (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump (0 : ComplexVector n) :=
  ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩

def outerChartBump (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump (0 : ComplexVector n) :=
  ⟨ρ / 2, ρ, by positivity, by linarith⟩

def chartWeight
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (ρ : ℝ) (hρ : 0 < ρ) :
    M.Carrier → ℝ := chartExtensionZero e (innerChartBump n ρ hρ)

def chartLocalization
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (ρ : ℝ) (hρ : 0 < ρ) :
    M.Carrier → ℝ := chartExtensionZero e (outerChartBump n ρ hρ)

theorem BoundedChartFamily.chartWeight_properties
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius) :
    HasCompactSupport (chartWeight (A.chart p) ρ hρ) ∧
      SmoothFn (chartWeight (A.chart p) ρ hρ) ∧
      tsupport (chartWeight (A.chart p) ρ hρ) ⊆ A.chart p '' closedBall 0 (ρ / 2) := by
  have hsource : tsupport (innerChartBump n ρ hρ) ⊆ (A.chart p).source := by
    rw [ContDiffBump.tsupport_eq]
    intro z hz
    apply A.closedBall_source p
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (by dsimp [innerChartBump]; linarith))
  obtain ⟨hc, hs, ht⟩ := chartExtensionZero_properties (A.chart p) (A.inverse_differentiable p)
    (innerChartBump n ρ hρ).contDiff (innerChartBump n ρ hρ).hasCompactSupport hsource
  refine ⟨hc, L18Aux.smoothFn_of_contMDiff_real hs, ?_⟩
  simpa only [chartWeight, ContDiffBump.tsupport_eq, innerChartBump] using ht

theorem BoundedChartFamily.chartLocalization_properties
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius) :
    HasCompactSupport (chartLocalization (A.chart p) ρ hρ) ∧
      SmoothFn (chartLocalization (A.chart p) ρ hρ) ∧
      tsupport (chartLocalization (A.chart p) ρ hρ) ⊆ A.chart p '' closedBall 0 ρ := by
  have hsource : tsupport (outerChartBump n ρ hρ) ⊆ (A.chart p).source := by
    rw [ContDiffBump.tsupport_eq]
    intro z hz
    apply A.closedBall_source p
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans hρr.le)
  obtain ⟨hc, hs, ht⟩ := chartExtensionZero_properties (A.chart p) (A.inverse_differentiable p)
    (outerChartBump n ρ hρ).contDiff (outerChartBump n ρ hρ).hasCompactSupport hsource
  refine ⟨hc, L18Aux.smoothFn_of_contMDiff_real hs, ?_⟩
  simpa only [chartLocalization, ContDiffBump.tsupport_eq, outerChartBump] using ht

theorem chartExtensionZero_mem_Icc
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    {φ : ComplexVector n → ℝ} (hφ : ∀ z, φ z ∈ Icc (0 : ℝ) 1) (y : M.Carrier) :
    chartExtensionZero e φ y ∈ Icc (0 : ℝ) 1 := by
  classical
  unfold chartExtensionZero
  split_ifs
  · exact hφ _
  · exact ⟨le_rfl, zero_le_one⟩

theorem chartExtensionZero_one_on_image
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    {φ : ComplexVector n → ℝ} {K : Set (ComplexVector n)}
    (hK : K ⊆ e.source) (hφ : ∀ z ∈ K, φ z = 1) {y : M.Carrier}
    (hy : y ∈ e '' K) : chartExtensionZero e φ y = 1 := by
  obtain ⟨z, hz, rfl⟩ := hy
  simp only [chartExtensionZero, ite_eq_left (e.map_source (hK hz)), e.left_inv (hK hz)]
  exact hφ z hz

theorem chartWeight_mem_Icc
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) {ρ : ℝ} (hρ : 0 < ρ)
    (y : M.Carrier) : chartWeight e ρ hρ y ∈ Icc (0 : ℝ) 1 :=
  chartExtensionZero_mem_Icc e (fun _ =>
    ⟨(innerChartBump n ρ hρ).nonneg, (innerChartBump n ρ hρ).le_one⟩) y

theorem chartLocalization_mem_Icc
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) {ρ : ℝ} (hρ : 0 < ρ)
    (y : M.Carrier) : chartLocalization e ρ hρ y ∈ Icc (0 : ℝ) 1 :=
  chartExtensionZero_mem_Icc e (fun _ =>
    ⟨(outerChartBump n ρ hρ).nonneg, (outerChartBump n ρ hρ).le_one⟩) y

theorem BoundedChartFamily.chartWeight_one
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius) {y : M.Carrier}
    (hy : y ∈ A.chart p '' closedBall 0 (ρ / 4)) :
    chartWeight (A.chart p) ρ hρ y = 1 := by
  apply chartExtensionZero_one_on_image (A.chart p) (K := closedBall 0 (ρ / 4)) _ _ hy
  · intro z hz
    apply A.closedBall_source p
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (by linarith))
  · intro z hz
    exact (innerChartBump n ρ hρ).one_of_mem_closedBall hz

theorem BoundedChartFamily.chartLocalization_one
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius) {y : M.Carrier}
    (hy : y ∈ A.chart p '' closedBall 0 (ρ / 2)) :
    chartLocalization (A.chart p) ρ hρ y = 1 := by
  apply chartExtensionZero_one_on_image (A.chart p) (K := closedBall 0 (ρ / 2)) _ _ hy
  · intro z hz
    apply A.closedBall_source p
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (by linarith))
  · intro z hz
    exact (outerChartBump n ρ hρ).one_of_mem_closedBall hz

theorem BoundedChartFamily.chartLocalization_mul_weight
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius) (y : M.Carrier) :
    chartLocalization (A.chart p) ρ hρ y * chartWeight (A.chart p) ρ hρ y =
      chartWeight (A.chart p) ρ hρ y := by
  by_cases hn : chartWeight (A.chart p) ρ hρ y = 0
  · simp only [hn, mul_zero]
  · have hy := (A.chartWeight_properties p hρ hρr).2.2 (subset_closure hn)
    rw [A.chartLocalization_one p hρ hρr hy, one_mul]

end Yau.LeafProofs.L17Aux
