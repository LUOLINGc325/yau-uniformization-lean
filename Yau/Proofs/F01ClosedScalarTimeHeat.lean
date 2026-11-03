import Yau.Proofs.F01NativeScalarTimeHeat
import Yau.Proofs.F01ClosedHeatContinuity

/-! The true subcaloric inequality for P_t holds at both original closed
time faces. Interior representatives are identified by derivative locality,
then the actual closed-slab heat operator passes to the boundary continuously. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem flowLogDetTime_closed_open_eq (α : HermitianField M)
    (h : ℝ → HermitianField M) {T t : ℝ} (ht : t ∈ Ioo 0 T) (x : M.Carrier) :
    flowLogDetTime α h (Icc 0 T) x t = flowLogDetTime α h (Ioo 0 T) x t := by
  unfold flowLogDetTime
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
    derivWithin_of_isOpen isOpen_Ioo ht]

theorem closed_slab_scalar_time_heat_nonpos
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (x : M.Carrier) :
    ∀ t ∈ Icc 0 T,
      fieldHeatWithin h (Icc 0 T) (fun s y => flowLogDetTime α h (Icc 0 T) y s) x t ≤ 0 := by
  have hPt := flowLogDetTime_smoothSpaceTime α hα h (uniqueDiffOn_Icc hT) hh
  apply continuous_closed_interval_nonpos_of_interior hT
    (fieldHeatWithin_time_continuous h hh hPt (uniqueDiffOn_Icc hT) x)
  intro t ht
  have hUopen : SmoothSpaceTime U (Ioo 0 T) := fun a =>
    (hU a).mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hhop : MetricFamilySmooth h (Ioo 0 T) := fun a i j =>
    (hh a i j).mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hlocal := native_scalar_time_heat_nonpos α hα h U isOpen_Ioo hhop hUopen
    (fun s hs => hpot s ⟨hs.1.le, hs.2.le⟩)
    (fun y s hs => (hpde y s ⟨hs.1.le, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)) x ht
  have htime : (fun s => flowLogDetTime α h (Icc 0 T) x s) =ᶠ[𝓝 t]
      (fun s => flowLogDetTime α h (Ioo 0 T) x s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact flowLogDetTime_closed_open_eq α h hs x
  have hspace : (fun y => flowLogDetTime α h (Icc 0 T) y t) =
      (fun y => flowLogDetTime α h (Ioo 0 T) y t) :=
    funext (fun y => flowLogDetTime_closed_open_eq α h ht y)
  unfold fieldHeatWithin at hlocal ⊢
  dsimp only at hlocal ⊢
  rw [derivWithin_of_isOpen isOpen_Ioo ht] at hlocal
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), htime.deriv_eq, hspace]
  exact hlocal

end Yau.NodeProofs.F01Aux
