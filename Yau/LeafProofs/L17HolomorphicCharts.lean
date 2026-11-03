import Yau.LeafProofs.L17HolomorphicRegularity
import Yau.LeafProofs.L17ChartNaturality

/-!
The original bounded-geometry charts need only their two native complex
differentiability hypotheses. Their coordinate maps inherit full regularity.
-/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

def forwardChartDomain
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (a : M.Carrier) :
    Set (ComplexVector n) :=
  e.source ∩ e ⁻¹' (extChartAt (ComplexModel n) a).source

def inverseChartDomain
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (a : M.Carrier) :
    Set (ComplexVector n) :=
  chartTarget a ∩ chartInv a ⁻¹' e.target

theorem forwardChartDomain_isOpen
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (a : M.Carrier) :
    IsOpen (forwardChartDomain e a) :=
  e.continuousOn.isOpen_inter_preimage e.open_source
    (isOpen_extChartAt_source (I := ComplexModel n) a)

theorem inverseChartDomain_isOpen
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (a : M.Carrier) :
    IsOpen (inverseChartDomain e a) :=
  (continuousOn_extChartAt_symm (I := ComplexModel n) a).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ComplexModel n) a) e.open_target

theorem forwardChart_differentiableOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (a : M.Carrier) :
    DifferentiableOn ℂ (fun z => chartPt a (e z)) (forwardChartDomain e a) := by
  have hc := mdifferentiableOn_extChartAt (I := ComplexModel n) (x := a)
  have hcomp := hc.comp (he.mono inter_subset_left)
    (show forwardChartDomain e a ⊆ e ⁻¹' (chartAt (ComplexVector n) a).source from
      fun z hz => by simpa only [extChartAt_source] using hz.2)
  exact hcomp.differentiableOn

theorem inverseChart_differentiableOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (a : M.Carrier) :
    DifferentiableOn ℂ (fun z => e.symm (chartInv a z)) (inverseChartDomain e a) := by
  have hc := mdifferentiableOn_extChartAt_symm (I := ComplexModel n) (x := a)
  have hcomp := hei.comp (hc.mono inter_subset_left)
    (show inverseChartDomain e a ⊆ chartInv a ⁻¹' e.target from fun z hz => hz.2)
  exact hcomp.differentiableOn

theorem forwardChart_contDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (a : M.Carrier) :
    ContDiffOn ℂ ∞ (fun z => chartPt a (e z)) (forwardChartDomain e a) :=
  L17Holomorphic.complexVector_contDiffOn (forwardChartDomain_isOpen e a)
    (forwardChart_differentiableOn e he a)

theorem inverseChart_contDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (a : M.Carrier) :
    ContDiffOn ℂ ∞ (fun z => e.symm (chartInv a z)) (inverseChartDomain e a) :=
  L17Holomorphic.complexVector_contDiffOn (inverseChartDomain_isOpen e a)
    (inverseChart_differentiableOn e hei a)

theorem forwardChart_real_contDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => chartPt a (e z)) (forwardChartDomain e a) :=
  (forwardChart_contDiffOn e he a).restrict_scalars ℝ

theorem inverseChart_real_contDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => e.symm (chartInv a z)) (inverseChartDomain e a) :=
  (inverseChart_contDiffOn e hei a).restrict_scalars ℝ

theorem coordinateDifferential_eq_fderiv
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ e.source)
    (ha : e z ∈ (extChartAt (ComplexModel n) a).source) :
    coordinateDifferential e a z = fderiv ℂ (fun w => chartPt a (e w)) z := by
  apply ContinuousLinearMap.ext
  intro v
  rw [coordinateDifferential_apply]
  have hez := (he z hz).mdifferentiableAt (e.open_source.mem_nhds hz)
  have hca : MDifferentiableAt (ComplexModel n) (ComplexModel n)
      (chartPt a) (e z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using ha)
  have hc := mfderiv_comp_apply z hca hez v
  rw [mfderiv_eq_fderiv] at hc
  change fderiv ℂ (fun w => chartPt a (e w)) z v =
    tangentCoords a (e z) (mfderiv (ComplexModel n) (ComplexModel n) e z v) at hc
  exact hc.symm

def transitionDomain
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier) :
    Set (ComplexVector n) := e.source ∩ e ⁻¹' d.target

theorem transitionDomain_isOpen
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier) :
    IsOpen (transitionDomain e d) :=
  e.continuousOn.isOpen_inter_preimage e.open_source d.open_target

theorem transition_contDiffOn
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hdi : MDifferentiableOn (ComplexModel n) (ComplexModel n) d.symm d.target) :
    ContDiffOn ℂ ∞ (fun z => d.symm (e z)) (transitionDomain e d) := by
  apply L17Holomorphic.complexVector_contDiffOn (transitionDomain_isOpen e d)
  exact (hdi.comp (he.mono inter_subset_left)
    (show transitionDomain e d ⊆ e ⁻¹' d.target from fun z hz => hz.2)).differentiableOn

theorem transition_real_contDiffOn
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hdi : MDifferentiableOn (ComplexModel n) (ComplexModel n) d.symm d.target) :
    ContDiffOn ℝ ∞ (fun z => d.symm (e z)) (transitionDomain e d) :=
  (transition_contDiffOn e d he hdi).restrict_scalars ℝ

end Yau.LeafProofs.L17Aux
