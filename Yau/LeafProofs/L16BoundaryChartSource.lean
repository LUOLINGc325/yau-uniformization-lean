import Yau.LeafProofs.L16ChartCoefficientHolder

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance boundaryChartSource_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartSource_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartSource_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartSource_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartSource_thirdGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartSource_thirdSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance

/-- Multiplying the actual pulled source by a buffered chart cutoff extends
    it over the artificial edges of the model half space. The true face is
    retained, and precisely the original corner condition is preserved. -/
theorem boundary_chart_cutoff_source_holder {n : ℕ} {O : Set (Space n)}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (e : Space n)
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hci : ContDiffOn ℝ 3 c.symm c.target)
    (hFaces : ∀ y ∈ c.source,
      (y ∈ closure O ↔ 0 ≤ inner ℝ e (c y)) ∧
      (y ∈ frontier O ↔ inner ℝ e (c y) = 0))
    {q : ℝ} (hq : 0 < q) (hTarget : Metric.closedBall (0 : Space n) (4*q) ⊆ c.target) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T F : ℝ) (f : Point n → ℝ),
      HolderBound α (cylinder (closure O) 0 T) f F →
      (∀ x ∈ frontier O, f (x,0) = 0) →
      HolderBound α (cylinder {y : Space n | 0 ≤ inner ℝ e y} 0 T)
        (fun p => innerPatchBump q hq 0 p.1*f (c.symm p.1,p.2)) (C*F) ∧
      ∀ y, inner ℝ e y = 0 → innerPatchBump q hq 0 y*f (c.symm y,0) = 0 := by
  let V : Set (Space n) := Metric.ball (0 : Space n) (3*q)
  let H : Set (Space n) := {y : Space n | 0 ≤ inner ℝ e y}
  let φ : Space n → ℝ := innerPatchBump q hq 0
  have hVBall : V ⊆ Metric.closedBall (0 : Space n) (4*q) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hVT : V ⊆ c.target := hVBall.trans hTarget
  have hMap : MapsTo c.symm (H∩V) (closure O) := by
    intro y hy
    apply (hFaces (c.symm y) (c.map_target (hVT hy.2))).1.mpr
    rw [c.right_inv (hVT hy.2)]
    exact hy.1
  obtain ⟨D,hD,hBound⟩ := compact_actual_three_jet_bound c.open_target
    (isCompact_closedBall (0 : Space n) (4*q)) hTarget hci
  have hLip : ∀ x ∈ H∩V, ∀ y ∈ H∩V, ‖c.symm x-c.symm y‖ ≤ D*‖x-y‖ := by
    intro x hx y hy
    exact (chart_actual_two_jet_lipschitz c.open_target (convex_closedBall (0 : Space n) (4*q))
      hTarget hci hBound (hVBall hx.2) (hVBall hy.2)).1
  obtain ⟨P,hP,hφ⟩ := innerPatchBump_global_holderBound hα hα1 hq (0 : Space n)
  have hSupport : tsupport φ ⊆ V := by
    rw [(innerPatchBump q hq 0).tsupport_eq]
    change Metric.closedBall (0 : Space n) (3*q/2) ⊆ Metric.ball 0 (3*q)
    exact Metric.closedBall_subset_ball (by linarith)
  refine ⟨2*P*(1+D^α),by positivity,?_⟩
  intro T F f hf hCorner
  have hfPull := holderBound_spatial_lipschitz_pullback hα.le hD.le c.symm hMap hLip hf
  have hfLocal : HolderBound α ((V×ˢ Set.univ)∩cylinder H 0 T)
      (fun p => f (c.symm p.1,p.2)) (F*(1+D^α)) :=
    holderBound_mono hfPull (fun p hp => ⟨⟨hp.2.1,hp.1.1⟩,hp.2.2⟩)
  have hφLocal := holderBound_mono hφ (subset_univ (cylinder H 0 T))
  have hZero : ∀ p ∈ cylinder H 0 T, p ∉ V×ˢ Set.univ → φ p.1 = 0 := by
    intro p hp hOut
    apply image_eq_zero_of_notMem_tsupport
    intro hSupp
    exact hOut ⟨hSupport hSupp,mem_univ _⟩
  refine ⟨?_,?_⟩
  · have hh := holderBound_smul_cutoff_extension hφLocal hfLocal hZero
    convert hh using 1
    ring
  · intro y hy
    by_cases hφy : φ y = 0
    · change φ y*f (c.symm y,0) = 0
      rw [hφy,zero_mul]
    · have hyV : y ∈ V := hSupport (subset_tsupport φ (Function.mem_support.mpr hφy))
      have hxF : c.symm y ∈ frontier O := by
        apply (hFaces (c.symm y) (c.map_target (hVT hyV))).2.mpr
        rw [c.right_inv (hVT hyV)]
        exact hy
      rw [hCorner _ hxF,mul_zero]

end Yau.LeafProofs.L16Aux
