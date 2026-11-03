import Yau.Proofs.F01MetricFamilyEntries
import Yau.LeafProofs.L17HolomorphicCharts

/-! Actual metric pullbacks are jointly smooth in any fixed holomorphic
chart on the original time set, retaining one-sided smoothness at its faces. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_pullback_contDiffOn (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => pullbackMatrix (h p.2) e p.1 i j)
      (e.source ×ˢ I) := by
  rintro ⟨z, t⟩ hzt
  let a := e z
  let D := forwardChartDomain e a
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have hDopen : IsOpen D := forwardChartDomain_isOpen e a
  have hzD : z ∈ D := ⟨hzt.1, mem_extChartAt_source a⟩
  have hT : ContDiffOn ℂ ∞ T D := forwardChart_contDiffOn e he a
  have hJac : ContDiffOn ℂ ∞ (fderiv ℂ T) D := hT.fderiv_of_isOpen hDopen (by simp)
  have hJ (p q : Fin n) : ContDiffOn ℝ ∞
      (fun y : ComplexVector n × ℝ => linearMatrix (fderiv ℂ T y.1) p q) (D ×ˢ I) := by
    have hJ0 : ContDiffOn ℂ ∞ (fun w => linearMatrix (fderiv ℂ T w) p q) D :=
      (EuclideanSpace.proj p : ComplexVector n →L[ℂ] ℂ).contDiff.comp_contDiffOn
        (hJac.clm_apply contDiffOn_const)
    exact (hJ0.restrict_scalars ℝ).comp contDiffOn_fst (fun _ hy => hy.1)
  have hTprod : ContDiffOn ℝ ∞ (fun y : ComplexVector n × ℝ => (T y.1, y.2))
      (D ×ˢ I) :=
    ((hT.restrict_scalars ℝ).comp contDiffOn_fst (fun _ hy => hy.1)).prodMk contDiffOn_snd
  have hG (p q : Fin n) : ContDiffOn ℝ ∞
      (fun y : ComplexVector n × ℝ => hMat (h y.2) a (T y.1) p q) (D ×ˢ I) := by
    apply (metricFamily_hMat_contDiffOn h hh a p q).comp hTprod
    intro y hy
    exact ⟨(extChartAt (ComplexModel n) a).map_source hy.1.2, hy.2⟩
  have hterm (p q : Fin n) : ContDiffOn ℝ ∞
      (fun y : ComplexVector n × ℝ => star (linearMatrix (fderiv ℂ T y.1) p i) *
        hMat (h y.2) a (T y.1) p q * linearMatrix (fderiv ℂ T y.1) q j) (D ×ˢ I) :=
    ((Complex.conjCLE.contDiff.comp_contDiffOn (hJ p i)).mul (hG p q)).mul (hJ q j)
  have hs : ContDiffOn ℝ ∞ (fun y : ComplexVector n × ℝ =>
      ((linearMatrix (fderiv ℂ T y.1))ᴴ * hMat (h y.2) a (T y.1) *
        linearMatrix (fderiv ℂ T y.1)) i j) (D ×ˢ I) := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul] using
      (ContDiffOn.sum (fun q (_ : q ∈ Finset.univ) =>
        ContDiffOn.sum (fun p (_ : p ∈ Finset.univ) => hterm p q)))
  have hactual : ContDiffOn ℝ ∞
      (fun y : ComplexVector n × ℝ => pullbackMatrix (h y.2) e y.1 i j) (D ×ˢ I) := by
    apply hs.congr
    intro y hy
    have hc := pullbackMatrix_eq_congruence (h y.2) e a y.1 hy.1.2
    rw [coordinateDifferential_eq_fderiv e he a hy.1.1 hy.1.2] at hc
    exact congrFun (congrFun hc i) j
  apply (hactual (z, t) ⟨hzD, hzt.2⟩).mono_of_mem_nhdsWithin
  have hn : {y : ComplexVector n × ℝ | y.1 ∈ D} ∈ 𝓝 (z, t) :=
    (hDopen.preimage continuous_fst).mem_nhds hzD
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with y hyD hy
  exact ⟨hyD, hy.2⟩

end Yau.NodeProofs.F01Aux
