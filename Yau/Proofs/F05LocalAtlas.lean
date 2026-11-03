import Yau.Proofs.F05PhysicalCharts
import Yau.Proofs.F05TotalizedCharts

/-! Packing a genuine local physical chart into the exact computed atlas format. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_physical_chart_properties (hn : 0 < n) (O : Set M.Carrier) (p x : M.Carrier)
    (ν : Option (RIdx n)) (c : OpenPartialHomeomorph (Space n) (Space n))
    (hC : F05PhysicalChart O p x ν c) :
    let F := F05TotalForward (F05Sentinel n hn) c
    let U := chartTarget x ∩ F ⁻¹' Metric.ball 0 3
    IsOpen U ∧ U ⊆ chartTarget x ∧
    ContDiffOn ℝ ∞ F U ∧ ContDiffOn ℝ ∞ c.symm (Metric.ball 0 3) ∧
    c.symm '' Metric.ball 0 3 ⊆ U ∧
    (∀ z ∈ Metric.ball 0 3, F (c.symm z) = z) ∧
    (∀ z ∈ U, c.symm (F z) = z) ∧
    ∀ z ∈ Metric.ball 0 3,
      (chartInv x (c.symm z) ∈ O ↔ ν.elim True (fun j => realCoord z j < 0)) ∧
      (chartInv x (c.symm z) ∈ closure O ↔ ν.elim True (fun j => realCoord z j ≤ 0)) ∧
      (chartInv x (c.symm z) ∈ frontier O ↔ ν.elim False (fun j => realCoord z j = 0)) := by
  obtain ⟨hpx,hpc,hcp,hcT,hbuffer,hc,hci,hfaces⟩ := hC
  dsimp only
  have hsource := F05TotalForward_source (F05Sentinel n hn) (F05Sentinel_norm n hn) c
    (chartTarget x) hcT
  have htarget : Metric.ball (0 : Space n) 3 ⊆ c.target := fun z hz => hbuffer
    ((Metric.closedBall_subset_closedBall (by norm_num : (3 : ℝ) ≤ 4))
      (Metric.ball_subset_closedBall hz))
  refine ⟨?_,inter_subset_left,?_,hci.mono htarget,?_,?_,?_,?_⟩
  · rw [hsource]
    exact c.isOpen_inter_preimage Metric.isOpen_ball
  · rw [hsource]
    exact F05TotalForward_contDiffOn (F05Sentinel n hn) c hc
  · rintro z ⟨y,hy,rfl⟩
    rw [hsource]
    exact (F05TotalForward_inverse_image (F05Sentinel n hn) c hbuffer hy).1
  · intro z hz
    exact (F05TotalForward_inverse_image (F05Sentinel n hn) c hbuffer hz).2
  · intro z hz
    rw [hsource] at hz
    exact F05TotalForward_left_inverse (F05Sentinel n hn) c hz.1
  · intro z hz
    have hm := hfaces (c.symm z) (c.map_target (htarget hz))
    rw [c.right_inv (htarget hz)] at hm
    cases ν <;> exact hm

theorem F05_physical_chart_derivative_bounds (hn : 0 < n) (O : Set M.Carrier) (p x : M.Carrier)
    (ν : Option (RIdx n)) (c : OpenPartialHomeomorph (Space n) (Space n))
    (hC : F05PhysicalChart O p x ν c) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.closedBall 0 2,
      ‖iteratedFDeriv ℝ k c.symm z‖ ≤ C ∧
      ‖iteratedFDeriv ℝ k (F05TotalForward (F05Sentinel n hn) c) (c.symm z)‖ ≤ C := by
  obtain ⟨hUopen,hUtarget,hF,hI,hImage,hRight,hLeft,hMem⟩ :=
    F05_physical_chart_properties hn O p x ν c hC
  have hKBall : Metric.closedBall (0 : Space n) 2 ⊆ Metric.ball 0 3 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hMap : MapsTo c.symm (Metric.closedBall 0 2)
      (chartTarget x ∩ (F05TotalForward (F05Sentinel n hn) c) ⁻¹' Metric.ball 0 3) := by
    intro z hz
    exact hImage ⟨z,hKBall hz,rfl⟩
  have hIJ : ContinuousOn (iteratedFDeriv ℝ k c.symm) (Metric.ball 0 3) :=
    ContinuousOn.continuousOn_iteratedFDeriv hI Metric.isOpen_ball (by simp)
  have hFJ : ContinuousOn (iteratedFDeriv ℝ k (F05TotalForward (F05Sentinel n hn) c))
      (chartTarget x ∩ (F05TotalForward (F05Sentinel n hn) c) ⁻¹' Metric.ball 0 3) :=
    ContinuousOn.continuousOn_iteratedFDeriv hF hUopen (by simp)
  have hFC := hFJ.comp (hI.continuousOn.mono hKBall) hMap
  obtain ⟨CI,hCI⟩ := (isCompact_closedBall (0 : Space n) 2).exists_bound_of_continuousOn (hIJ.mono hKBall)
  obtain ⟨CF,hCF⟩ := (isCompact_closedBall (0 : Space n) 2).exists_bound_of_continuousOn hFC
  refine ⟨1+|CI|+|CF|,by positivity,?_⟩
  intro z hz
  exact ⟨(hCI z hz).trans (by linarith [le_abs_self CI,abs_nonneg CI,abs_nonneg CF]),
    (hCF z hz).trans (by linarith [le_abs_self CF,abs_nonneg CI,abs_nonneg CF])⟩

end Yau.Proofs.F05Aux
