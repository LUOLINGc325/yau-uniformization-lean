import Yau.LeafProofs.L17UniformPartition
import Yau.LeafProofs.L17ChartNaturality

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricSmoothAux
open L17Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual inverse-chart differential recovers the original fixed-chart frame. -/
theorem inverseChart_frame
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (c : M.Carrier) {w : ComplexVector n} (hw : w∈inverseChartDomain e c)
    (v : ComplexVector n) :
    mfderiv (ComplexModel n) (ComplexModel n) e (e.symm (chartInv c w))
      (fderiv ℂ (fun a => e.symm (chartInv c a)) w v)=
      chartVec c (chartInv c w) v := by
  let psi : ComplexVector n → ComplexVector n := fun a => e.symm (chartInv c a)
  have hO := (inverseChartDomain_isOpen e c).mem_nhds hw
  have hpsi : DifferentiableAt ℂ psi w :=
    ((inverseChart_contDiffOn e hei c).contDiffAt hO).differentiableAt (by simp)
  have hpsiM : MDifferentiableAt (ComplexModel n) (ComplexModel n) psi w :=
    mdifferentiableAt_iff_differentiableAt.mpr hpsi
  have heAt := (he (psi w) (e.map_target hw.2)).mdifferentiableAt
    (e.open_source.mem_nhds (e.map_target hw.2))
  have hEqual : (e ∘ psi)=ᶠ[𝓝 w] chartInv c := by
    filter_upwards [hO] with a ha
    exact e.right_inv ha.2
  have hDeriv := hEqual.mfderiv_eq (I := ComplexModel n) (I' := ComplexModel n)
  have hChain := mfderiv_comp_apply w heAt hpsiM v
  rw [hDeriv,mfderiv_eq_fderiv] at hChain
  have hCoord : chartPt c (chartInv c w)=w :=
    (extChartAt (ComplexModel n) c).right_inv hw.1
  calc
    _ = mfderiv (ComplexModel n) (ComplexModel n) (chartInv c) w v := by
      convert! hChain.symm using 1
    _ = chartVec c (chartInv c w) v := by
      unfold chartVec
      rw [hCoord]
      rfl

/-- The original real metric is the finite tensor pullback in one fixed pair
of charts, with the original factor two and actual complex derivative. -/
theorem realMetricFn_eq_inverseChart_pullback
    (h : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (c : M.Carrier) {w : ComplexVector n} (hw : w∈inverseChartDomain e c)
    (a b : RIdx n) :
    realMetricFn h c w a b=2*(∑ i, ∑ j,
      star ((fderiv ℂ (fun z => e.symm (chartInv c z)) w (realVec a)) i)*
        (pullbackMatrix h e (e.symm (chartInv c w)) i j*
          ((fderiv ℂ (fun z => e.symm (chartInv c z)) w (realVec b)) j))).re := by
  have hTensor := pullbackMatrix_sesquilinear h e (e.symm (chartInv c w))
    (fderiv ℂ (fun z => e.symm (chartInv c z)) w (realVec a))
    (fderiv ℂ (fun z => e.symm (chartInv c z)) w (realVec b))
  rw [inverseChart_frame e he hei c hw (realVec a),
    inverseChart_frame e he hei c hw (realVec b),e.right_inv hw.2] at hTensor
  have hReal := congrArg (fun z : ℂ => 2*z.re) hTensor.symm
  simpa only [realMetricFn,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum] using hReal

/-- Every component of the actual complex inverse-chart differential is
real smooth on the genuine open inverse-chart domain. -/
theorem inverseChart_derivative_component_contDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (c : M.Carrier) (a : RIdx n) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun w => (fderiv ℂ (fun z => e.symm (chartInv c z)) w (realVec a)) i)
      (inverseChartDomain e c) := by
  have hD : ContDiffOn ℂ ∞ (fderiv ℂ (fun z => e.symm (chartInv c z)))
      (inverseChartDomain e c) :=
    (inverseChart_contDiffOn e hei c).fderiv_of_isOpen (inverseChartDomain_isOpen e c) (by simp)
  have hApply := hD.clm_apply (contDiffOn_const (c := realVec a))
  exact ((EuclideanSpace.proj i).contDiff.comp_contDiffOn hApply).restrict_scalars ℝ

end Yau.LeafProofs.L17BootstrapMetricSmoothAux
