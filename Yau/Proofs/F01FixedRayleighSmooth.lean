import Yau.Proofs.F01ChartGramSmooth
import Yau.Proofs.F01RayleighOrder

/-! A fixed nonzero coordinate direction gives a smooth actual Rayleigh
quotient. Its denominator is positive by the genuine metric pullback. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem matrixQuadraticValue_contDiffAt
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (z : ComplexVector n)
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z) :
    ContDiffAt ℝ ∞ (fun w => matrixQuadraticValue (G w) v) z := by
  have hh : ContDiffAt ℝ ∞ (fun w => ∑ i, star (v i) * ∑ j, G w i j * v j) z :=
    ContDiffAt.sum (fun i (_ : i ∈ Finset.univ) => contDiffAt_const.mul
      (ContDiffAt.sum (fun j (_ : j ∈ Finset.univ) => (hG i j).mul contDiffAt_const)))
  exact Complex.reCLM.contDiff.contDiffAt.comp z hh

theorem fixed_rayleigh_contDiffAt (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) {v : Fin n → ℂ} (hv : v ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => matrixRayleigh (pullbackMatrix g e w) (pullbackMatrix k e w) v) z := by
  have hnum := matrixQuadraticValue_contDiffAt (pullbackMatrix k e) v z
    (fun i j => pullbackMatrix_entry_contDiffAt k hk e he hz i j)
  have hden := matrixQuadraticValue_contDiffAt (pullbackMatrix g e) v z
    (fun i j => pullbackMatrix_entry_contDiffAt g hg e he hz i j)
  exact hnum.div hden (matrixQuadraticValue_pos (pullbackMatrix_posDef g e he hei hz) hv).ne'

end Yau.NodeProofs.F01Aux
