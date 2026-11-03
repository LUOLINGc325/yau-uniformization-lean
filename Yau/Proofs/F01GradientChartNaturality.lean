import Yau.Proofs.F01DualNormCongruence
import Yau.Proofs.F01WirtingerCoordinateChain
import Yau.Proofs.F01KahlerMixedExchange
import Yau.Proofs.F01ScalarChartSmooth
import Yau.LeafProofs.L14Curvature

/-! The actual scalar Wirtinger covector transforms by the transpose
Jacobian, so its pullback cotangent norm is exactly the native gradient norm. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem wirt_direction_coordinates (f : ComplexVector n → ℂ) (z v : ComplexVector n) :
    wirt f z v = ∑ i, v i * wirt f z (stdVec i) := by
  exact Yau.LeafProofs.L14Aux.wirt_direction_coordinates f z v

theorem wirt_covector_comp (T : ComplexVector n → ComplexVector n)
    (f : ComplexVector n → ℂ) (z : ComplexVector n)
    (hT : DifferentiableAt ℂ T z) (hf : DifferentiableAt ℝ f (T z)) :
    (fun i => wirt (fun w => f (T w)) z (stdVec i)) =
      (linearMatrix (fderiv ℂ T z))ᵀ *ᵥ (fun i => wirt f (T z) (stdVec i)) := by
  funext i
  rw [wirt_comp_complex_differentiable T f z (stdVec i) hT hf,
    wirt_direction_coordinates]
  rfl

theorem dualNormMat_holomorphic_chart_gradient (g : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    dualNormMat (pullbackMatrix g e z) (WithLp.toLp 2
      (fun i => wirt (fun w => (f (e w) : ℂ)) z (stdVec i))) = gradNormSq g f (e z) := by
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hzD : z ∈ forwardChartDomain e a := ⟨hz, ha⟩
  have hT : DifferentiableAt ℂ T z :=
    ((forwardChart_contDiffOn e he a).contDiffAt
      ((forwardChartDomain_isOpen e a).mem_nhds hzD)).differentiableAt (by simp)
  have hfa : DifferentiableAt ℝ (fun w => ((inChart a f w : ℝ) : ℂ)) (T z) := by
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((hf a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
        ((extChartAt (ComplexModel n) a).map_source ha)))).differentiableAt (by simp)
  have hgerm : (fun w => (f (e w) : ℂ)) =ᶠ[𝓝 z]
      (fun w => ((inChart a f (T w) : ℝ) : ℂ)) := by
    filter_upwards [(forwardChartDomain_isOpen e a).mem_nhds hzD] with w hw
    change (f (e w) : ℂ) = (f (chartInv a (chartPt a (e w))) : ℂ)
    exact congrArg (fun p => (f p : ℂ)) ((extChartAt (ComplexModel n) a).left_inv hw.2).symm
  have hvec : (fun i => wirt (fun w => (f (e w) : ℂ)) z (stdVec i)) =
      (linearMatrix (coordinateDifferential e a z))ᵀ *ᵥ
        (fun i => wirt (fun w => ((inChart a f w : ℝ) : ℂ)) (T z) (stdVec i)) := by
    have hh := wirt_covector_comp T (fun w => ((inChart a f w : ℝ) : ℂ)) z hT hfa
    rw [← coordinateDifferential_eq_fderiv e he a hz ha] at hh
    exact (funext (fun i => wirt_eq_of_eventuallyEq hgerm (stdVec i))).trans hh
  rw [hvec, pullbackMatrix_eq_congruence g e a z ha,
    dualNormMat_congruence _ _ (linearMatrix_det_ne_zero _
      (coordinateDifferential_injective e he hei a hz ha))]
  rfl

end Yau.NodeProofs.F01Aux
