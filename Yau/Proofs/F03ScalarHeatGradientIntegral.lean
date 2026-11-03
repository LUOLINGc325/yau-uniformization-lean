import Yau.Proofs.F03ScalarHeatDerivativeIntegral
import Yau.Proofs.F03WirtingerDifferential

/-! The actual physical gradient obeys the genuine triangle inequality under the zero-endpoint heat-time integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sqrt_gradNormSq_negative (g : HermitianField M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => -f y) x)=Real.sqrt (gradNormSq g f x) := by
  have hn : SmoothFn (fun y => -f y) := fun a => (hf a).neg
  rw [sqrt_gradNormSq_eq_factor_norm g _ hn x,sqrt_gradNormSq_eq_factor_norm g f hf x]
  have he : inChart x (fun y => -f y)=(fun z => -inChart x f z) := rfl
  rw [he,fderiv_fun_neg,map_neg,map_neg,norm_neg]

theorem boundedScalarHeat_gradient_timeIntegral_le
    (g : HermitianField M) (f : M.Carrier → ℝ) (u : ℝ → M.Carrier → ℝ)
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u)
    (x : M.Carrier) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun b => Real.sqrt (gradNormSq g (u b) x)) volume 0 R ∧
      Real.sqrt (gradNormSq g (fun y => ∫ b in (0:ℝ)..R,u b y) x) ≤
        ∫ b in (0:ℝ)..R,Real.sqrt (gradNormSq g (u b) x) := by
  let A := (dualNormFactor (gMat g x)).comp (realWirtingerMap n)
  let D : ℝ → ComplexVector n →L[ℝ] ℝ := fun b => fderiv ℝ (inChart x (u b)) (chartPt x x)
  have hIntD : IntegrableOn D (Ioc 0 R) volume :=
    boundedScalarHeat_spatialDerivative_integrableOn g f u hf hu x (mem_extChartAt_target x) R
  have hEq : (fun b => ‖A (D b)‖)=ᵐ[volume.restrict (Ioc 0 R)]
      (fun b => Real.sqrt (gradNormSq g (u b) x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with b hb
    rw [sqrt_gradNormSq_eq_factor_norm g (u b) (LeafProofs.L19Aux.smoothSpaceTime_slice hu.1 hb.1) x]
    rfl
  have hIntGradient : IntegrableOn (fun b => Real.sqrt (gradNormSq g (u b) x)) (Ioc 0 R) volume :=
    (A.integrable_comp hIntD).norm.congr hEq
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr hIntGradient,?_⟩
  have hSmooth := boundedScalarHeat_timeIntegral_smooth g f u hf hu hR
  rw [sqrt_gradNormSq_eq_factor_norm g _ hSmooth x,
    boundedScalarHeat_timeIntegral_chart_derivative g f u hf hu x
      (z := chartPt x x) (mem_extChartAt_target x) hR]
  change ‖A (∫ b in (0:ℝ)..R,D b)‖ ≤ _
  rw [intervalIntegral.integral_of_le hR,intervalIntegral.integral_of_le hR,
    ← A.integral_comp_comm hIntD]
  calc
    _ ≤ ∫ b in Ioc (0:ℝ) R,‖A (D b)‖ := norm_integral_le_integral_norm (fun b => A (D b))
    _ = _ := integral_congr_ae hEq

end Yau.Proofs.F03Aux
