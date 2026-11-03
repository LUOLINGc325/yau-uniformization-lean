import Yau.Proofs.F01HolomorphicMatrixInverse
import Yau.Proofs.F01ChartGramSmooth
import Yau.LeafProofs.L14Gauge

/-! Genuine curvature transport into an arbitrary actual holomorphic
parametrization, reusing the native holomorphic gauge theorem. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix Topology ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem curvatureMatrix_holomorphic_chart (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (i j : Fin n) :
    let J := linearMatrix (coordinateDifferential e (e z) z)
    BundleDbar.curvatureMatrix (pullbackMatrix g e) z i j =
      Jᴴ * (∑ p, ∑ q, (J p i * star (J q j)) •
        BundleDbar.curvatureMatrix (hMat g (e z)) (chartPt (e z) (e z)) p q) * J := by
  let a := e z
  let O := forwardChartDomain e a
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  let A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ := fun w => linearMatrix (fderiv ℂ T w)
  let C : ComplexVector n → Matrix (Fin n) (Fin n) ℂ := fun w => (A w)⁻¹
  have hO : IsOpen O := forwardChartDomain_isOpen e a
  have hzO : z ∈ O := ⟨hz, mem_extChartAt_source a⟩
  have hT : ContDiffOn ℂ ∞ T O := forwardChart_contDiffOn e he a
  have hTU : MapsTo T O (chartTarget a) := by
    intro w hw
    exact (extChartAt (ComplexModel n) a).map_source hw.2
  have hA (i j : Fin n) : ContDiffOn ℂ ∞ (fun w => A w i j) O :=
    holomorphic_jacobian_entry_contDiffOn hO hT i j
  have hdetA : ∀ w ∈ O, (A w).det ≠ 0 := by
    intro w hw
    change (linearMatrix (fderiv ℂ T w)).det ≠ 0
    rw [← coordinateDifferential_eq_fderiv e he a hw.1 hw.2]
    exact linearMatrix_det_ne_zero _ (coordinateDifferential_injective e he hei a hw.1 hw.2)
  have hC (i j : Fin n) : ContDiffOn ℂ ∞ (fun w => C w i j) O :=
    complex_contDiffOn_matrix_inv hA hdetA i j
  have hAC : ∀ w ∈ O, A w * C w = 1 := by
    intro w hw
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdetA w hw))
  have hH := hMat_contDiffOn_of_metricSmooth g hg a
  have hdetH : ∀ w ∈ chartTarget a, (hMat g a w).det ≠ 0 := by
    intro w hw
    exact ((Yau.LeafProofs.L12Aux.hMat_posDef g a w hw).isUnit.map Matrix.detMonoidHom).ne_zero
  have heq : EqOn (pullbackMatrix g e) (fun w => (A w)ᴴ * hMat g a (T w) * A w) O := by
    intro w hw
    rw [pullbackMatrix_eq_congruence g e a w hw.2,
      coordinateDifferential_eq_fderiv e he a hw.1 hw.2]
  rw [Yau.LeafProofs.L14Aux.curvatureMatrix_congr_of_eqOn _ _ hO heq z hzO]
  have hh := Yau.LeafProofs.L14Aux.curvatureMatrix_holomorphic_change hO
    (isOpen_extChartAt_target a) (hMat g a) T A C hH hdetH hT hTU hA hC hAC z hzO i j
  have hAz : A z = linearMatrix (coordinateDifferential e a z) := by
    dsimp only [A]
    rw [← coordinateDifferential_eq_fderiv e he a hz (mem_extChartAt_source a)]
  rw [hAz, ← coordinateDifferential_eq_fderiv e he a hz (mem_extChartAt_source a)] at hh
  exact hh

end Yau.NodeProofs.F01Aux
