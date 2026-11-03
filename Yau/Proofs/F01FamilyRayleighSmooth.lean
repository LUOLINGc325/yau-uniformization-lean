import Yau.Proofs.F01FamilyChartGram
import Yau.Proofs.F01MetricFamilySlices
import Yau.Proofs.F01RayleighOrder

/-! The fixed-direction Rayleigh test has the actual joint smoothness on
the original closed time interval required for a parabolic contact. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem matrixQuadraticValue_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (S : Set E)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun w => G w i j) S) :
    ContDiffOn ℝ ∞ (fun w => matrixQuadraticValue (G w) v) S := by
  have hh : ContDiffOn ℝ ∞ (fun w => ∑ i, star (v i) * ∑ j, G w i j * v j) S :=
    ContDiffOn.sum (fun i (_ : i ∈ Finset.univ) => contDiffOn_const.mul
      (ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) => (hG i j).mul contDiffOn_const)))
  exact Complex.reCLM.contDiff.comp_contDiffOn hh

theorem metricFamily_fixed_rayleigh_contDiffOn (g : HermitianField M)
    (hg : MetricSmooth g) (k : ℝ → HermitianField M) {I : Set ℝ}
    (hk : MetricFamilySmooth k I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {v : Fin n → ℂ} (hv : v ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      matrixRayleigh (pullbackMatrix g e p.1) (pullbackMatrix (k p.2) e p.1) v)
      (e.source ×ˢ I) := by
  have hnum := matrixQuadraticValue_contDiffOn
    (fun p : ComplexVector n × ℝ => pullbackMatrix (k p.2) e p.1) v (e.source ×ˢ I)
    (fun i j => metricFamily_pullback_contDiffOn k hk e he i j)
  have hden := matrixQuadraticValue_contDiffOn
    (fun p : ComplexVector n × ℝ => pullbackMatrix g e p.1) v (e.source ×ˢ I)
    (fun i j => metricFamily_pullback_contDiffOn (fun _ => g) (metricFamilySmooth_const hg I) e he i j)
  apply hnum.div hden
  intro p hp
  exact (matrixQuadraticValue_pos (pullbackMatrix_posDef g e he hei hp.1) hv).ne'

end Yau.NodeProofs.F01Aux
