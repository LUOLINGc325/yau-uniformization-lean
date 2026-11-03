import Yau.Proofs.F01LocalFlowTime

/-! The original closed-slab potential PDE gives the actual metric jet
at every positive time inside the supplied short-time interval. The target
derivative may be taken on any closed comparison slab. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem shortTime_potential_chart_real_hasDerivWithinAt
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ}
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (Real.log ((gMat (h s) x).det.re / (gMat α x).det.re)) (Icc 0 T) s)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (J : Set ℝ) (i j : Fin n) :
    HasDerivWithinAt (fun s => (pullbackMatrix (h s) e z i j).re)
      (leviC (fun w => Real.log (pullbackMatrix (h t) e w).det.re) z i j).re J t := by
  have hUopen : SmoothSpaceTime U (Ioo 0 T) := fun a =>
    (hU a).mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hpdeOpen : ∀ x s, s ∈ Ioo 0 T → HasDerivAt (U x)
      (Real.log ((gMat (h s) x).det.re / (gMat α x).det.re)) s := by
    intro x s hs
    exact (hpde x s ⟨hs.1.le, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hcomplex := flow_potential_chart_matrix_hasDerivAt α hα h U isOpen_Ioo hUopen
    (fun s hs => hpot s ⟨hs.1.le, hs.2.le⟩) hpdeOpen e he hei hz ht i j
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomplex).hasDerivWithinAt

end Yau.NodeProofs.F01Aux
