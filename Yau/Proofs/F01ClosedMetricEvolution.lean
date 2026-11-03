import Yau.Proofs.F01ClosedTimeODE
import Yau.Proofs.F01ClosedRicciFamily
import Yau.Proofs.F01NativeMetricEvolution

/-! The original closed-slab scalar potential equation yields the actual
metric evolution at both faces; no time extension of the solution is assumed. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem closed_slab_potential_metric_evolution
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (Real.log ((gMat (h s) x).det.re / (gMat α x).det.re)) (Icc 0 T) s)
    (x : M.Carrier) (i j : Fin n) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => gMat (h s) x i j)
      (-ricci (h t) x i j) (Icc 0 T) t := by
  have hUopen : SmoothSpaceTime U (Ioo 0 T) := fun a =>
    (hU a).mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hpdeOpen : ∀ y s, s ∈ Ioo 0 T → HasDerivAt (U y)
      (Real.log ((gMat (h s) y).det.re / (gMat α y).det.re)) s := by
    intro y s hs
    exact (hpde y s ⟨hs.1.le, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  apply closed_interval_ode_of_interior hT (metricFamily_gMat_time_smooth h hh x i j)
    (metricFamily_ricci_time_smooth h (uniqueDiffOn_Icc hT) hh x i j).neg.continuousOn
  intro t ht
  exact flow_potential_native_metric_hasDerivAt α hα h U isOpen_Ioo hUopen
    (fun s hs => hpot s ⟨hs.1.le, hs.2.le⟩) hpdeOpen x ht i j

end Yau.NodeProofs.F01Aux
