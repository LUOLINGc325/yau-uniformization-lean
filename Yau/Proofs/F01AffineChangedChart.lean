import Yau.Proofs.F01AffineCoordinate
import Yau.Proofs.F01PullbackComposition

/-! Actual affine changes of holomorphic manifold charts and their Gram
matrices, with the native complex manifold chain rule. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def affineChangedChart (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (z0 : ComplexVector n) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    OpenPartialHomeomorph (ComplexVector n) M.Carrier :=
  (affineCoordinateHomeomorph z0 A hA).toOpenPartialHomeomorph.trans e

theorem affineChangedChart_center
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (z0 : ComplexVector n) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    affineChangedChart e z0 A hA 0 = e z0 := by
  change e (z0 + matrixCoordinateEquiv A hA 0) = e z0
  simp

theorem affineChangedChart_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (z0 : ComplexVector n) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (affineChangedChart e z0 A hA) (affineChangedChart e z0 A hA).source := by
  apply he.comp (affineCoordinateHomeomorph_contDiff z0 A hA).contMDiff.contMDiffOn
  intro z hz
  exact hz.2

theorem affineChangedChart_inverse_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target)
    (z0 : ComplexVector n) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (affineChangedChart e z0 A hA).symm (affineChangedChart e z0 A hA).target := by
  apply (affineCoordinateHomeomorph_inverse_contDiff z0 A hA).contMDiff.comp_contMDiffOn
  apply he.mono
  intro z hz
  exact hz.1

theorem affineChangedChart_pullbackMatrix (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (z0 : ComplexVector n) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A)
    {z : ComplexVector n} (hz : z ∈ (affineChangedChart e z0 A hA).source) :
    pullbackMatrix g (affineChangedChart e z0 A hA) z =
      Aᴴ * pullbackMatrix g e (z0 + matrixCoordinateEquiv A hA z) * A := by
  have heAt : MDifferentiableAt (ComplexModel n) (ComplexModel n) e
      (affineCoordinateHomeomorph z0 A hA z) :=
    ((he _ hz.2).contMDiffAt (e.open_source.mem_nhds hz.2)).mdifferentiableAt (by simp)
  have hp := pullbackMatrix_coordinate_composition g heAt
    (affineCoordinateHomeomorph_contDiff z0 A hA).contDiffAt
  rw [(affineCoordinateHomeomorph_hasFDerivAt z0 A hA z).fderiv,
    matrixCoordinateEquiv_native_matrix] at hp
  exact hp

end Yau.NodeProofs.F01Aux
