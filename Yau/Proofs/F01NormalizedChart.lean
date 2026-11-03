import Yau.Proofs.F01AffineChangedChart
import Yau.Proofs.F01SimultaneousHermitian
import Yau.Proofs.F01OrdinaryMetricData

/-! Actual holomorphic charts centered at the chosen point, with identity
background Gram matrix and diagonal second metric at that point. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_normalized_holomorphic_chart (g k : HermitianField M) (p : M.Carrier) :
    ∃ e : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      e 0 = p ∧ (0 : ComplexVector n) ∈ e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target ∧
      pullbackMatrix g e 0 = 1 ∧
      ∃ values : Fin n → ℝ,
        pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)) := by
  let z0 : ComplexVector n := chartPt p p
  let H := pullbackMatrix g (ordinaryChart p) z0
  let K := pullbackMatrix k (ordinaryChart p) z0
  have hH : H.PosDef := ordinary_gram_posDef g p (mem_extChartAt_target p)
  have hK : K.IsHermitian := pullbackMatrix_isHermitian k (ordinaryChart p) z0
  obtain ⟨A, hA, hAH, values, hAK⟩ := simultaneous_hermitian_normalization H K hH hK
  let e := affineChangedChart (ordinaryChart p) z0 A hA
  have he0 : e 0 = p := by
    rw [affineChangedChart_center]
    simp only [ordinaryChart_apply, z0, chartInv, chartPt]
    exact (extChartAt (ComplexModel n) p).left_inv (mem_extChartAt_source p)
  have hs : (0 : ComplexVector n) ∈ e.source := by
    change (0 : ComplexVector n) ∈ Set.univ ∧
      affineCoordinateHomeomorph z0 A hA 0 ∈ (ordinaryChart p).source
    refine ⟨Set.mem_univ _, ?_⟩
    rw [affineCoordinateHomeomorph_apply, map_zero, add_zero, ordinaryChart_source]
    exact mem_extChartAt_target p
  refine ⟨e, he0, hs,
    affineChangedChart_contMDiffOn (ordinaryChart p) (ordinaryChart_contMDiffOn p) z0 A hA,
    affineChangedChart_inverse_contMDiffOn (ordinaryChart p) (ordinaryChart_inverse_contMDiffOn p) z0 A hA,
    ?_, values, ?_⟩
  · have h := affineChangedChart_pullbackMatrix g (ordinaryChart p)
      (ordinaryChart_contMDiffOn p) z0 A hA hs
    have hp : pullbackMatrix g e 0 = Aᴴ * H * A := by
      simpa only [map_zero, add_zero] using h
    exact hp.trans hAH
  · have h := affineChangedChart_pullbackMatrix k (ordinaryChart p)
      (ordinaryChart_contMDiffOn p) z0 A hA hs
    have hp : pullbackMatrix k e 0 = Aᴴ * K * A := by
      simpa only [map_zero, add_zero] using h
    exact hp.trans hAK

end Yau.NodeProofs.F01Aux
