import Yau.Proofs.F01ChartGramSmooth
import Yau.Proofs.F01ConstantFrameZeroJet
import Yau.Proofs.F01ChartComposition
import Yau.Proofs.F01SimultaneousHermitian

/-! Diagonalizing a second metric by an actual linear coordinate change
preserves the vanishing real background jet. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix ComplexOrder Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem diagonalize_second_metric_in_normal_chart (g k : HermitianField M)
    (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hs : (0 : ComplexVector n) ∈ e.source)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (hei : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target)
    (hvalue : pullbackMatrix g e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w => pullbackMatrix g e w i j) 0 = 0) :
    ∃ q : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      q 0 = e 0 ∧ (0 : ComplexVector n) ∈ q.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ q q.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ q.symm q.target ∧
      pullbackMatrix g q 0 = 1 ∧
      (∀ i j, fderiv ℝ (fun w => pullbackMatrix g q w i j) 0 = 0) ∧
      ∃ values : Fin n → ℝ,
        pullbackMatrix k q 0 = Matrix.diagonal (fun i => (values i : ℂ)) := by
  let K := pullbackMatrix k e 0
  obtain ⟨A, hA, hAI, values, hAK⟩ := simultaneous_hermitian_normalization
    (1 : Matrix (Fin n) (Fin n) ℂ) K Matrix.PosDef.one
      (pullbackMatrix_isHermitian k e 0)
  let q := affineChangedChart e 0 A hA
  have hq0 : (0 : ComplexVector n) ∈ q.source :=
    affineChangedChart_zero_source e 0 hs A hA
  have hT0 : (0 : ComplexVector n) + matrixCoordinateEquiv A hA 0 = 0 := by simp
  have hgram : ∀ i j, (fun w => pullbackMatrix g q w i j) =ᶠ[𝓝 (0 : ComplexVector n)]
      (fun w => (Aᴴ * pullbackMatrix g e (0 + matrixCoordinateEquiv A hA w) * A) i j) := by
    intro i j
    filter_upwards [q.open_source.mem_nhds hq0] with w hw
    exact congrFun (congrFun (affineChangedChart_pullbackMatrix g e he 0 A hA hw) i) j
  refine ⟨q, affineChangedChart_center e 0 A hA, hq0,
    affineChangedChart_contMDiffOn e he 0 A hA,
    affineChangedChart_inverse_contMDiffOn e hei 0 A hA, ?_, ?_, values, ?_⟩
  · calc
      pullbackMatrix g q 0 = Aᴴ * pullbackMatrix g e 0 * A := by
        simpa only [hT0] using affineChangedChart_pullbackMatrix g e he 0 A hA hq0
      _ = 1 := by rw [hvalue]; exact hAI
  · intro i j
    refine (hgram i j).fderiv_eq.trans ?_
    apply constant_congruence_real_jet_zero
    · exact ((affineCoordinateHomeomorph_contDiff 0 A hA).restrict_scalars ℝ).contDiffAt.differentiableAt
        (by simp)
    · intro p r
      rw [hT0]
      exact (pullbackMatrix_entry_contDiffAt g hg e (he.mdifferentiableOn (by simp)) hs p r).differentiableAt
        (by simp)
    · intro p r
      rw [hT0]
      exact hjet p r
  · calc
      pullbackMatrix k q 0 = Aᴴ * K * A := by
        simpa only [hT0] using affineChangedChart_pullbackMatrix k e he 0 A hA hq0
      _ = _ := hAK

end Yau.NodeProofs.F01Aux
