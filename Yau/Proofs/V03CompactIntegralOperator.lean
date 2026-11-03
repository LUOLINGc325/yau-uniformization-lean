import Yau.Proofs.V03RealTraceDerivative
import Yau.Proofs.V03LeviChain
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Integration of a genuine compact uniform trace is a bounded linear
operator and commutes with its actual first and second real derivatives. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem compactContinuousMap_integrable {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(K, ℝ)) : Integrable f μ := by
  have he : (BoundedContinuousFunction.mkOfCompact f : K → ℝ) = (f : K → ℝ) := by
    funext x
    rfl
  rw [← he]
  exact (BoundedContinuousFunction.mkOfCompact f).integrable μ

def compactIntegralL {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] : C(K, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (compactContinuousMap_integrable μ f)
        (compactContinuousMap_integrable μ g)
      map_smul' := fun c f => integral_smul c f }
    (μ.real Set.univ) (fun f => by
      change ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖
      have hh := norm_integral_le_of_norm_le_const
        (μ := μ) (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
      simpa only [mul_comm] using hh)

theorem fderiv_comp_realCLM {P F G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {u : P → F} {z : P} (hu : DifferentiableAt ℝ u z) (v : P) :
    fderiv ℝ (fun p => L (u p)) z v = L (fderiv ℝ u z v) := by
  have hh := L.hasFDerivAt.comp z hu.hasFDerivAt
  exact congrArg (fun A : P →L[ℝ] G => A v) hh.fderiv

theorem secondFDeriv_comp_realCLM {P F G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {u : P → F} {z : P} (hu : ContDiffAt ℝ 2 u z) (w v : P) :
    fderiv ℝ (fderiv ℝ (fun p => L (u p))) z w v = L (fderiv ℝ (fderiv ℝ u) z w v) := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hLu : ContDiffAt ℝ 2 (fun p => L (u p)) z := L.contDiff.comp_contDiffAt z hu
  have hdLu := (hLu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_real_clm_apply hdLu w v]
  have heq : (fun p => fderiv ℝ (fun p' => L (u p')) p v) =ᶠ[𝓝 z]
      (fun p => L (fderiv ℝ u p v)) := by
    filter_upwards [hu.eventually (by norm_num)] with p hp
    exact fderiv_comp_realCLM L (hp.differentiableAt (by norm_num)) v
  rw [heq.fderiv_eq, fderiv_comp_realCLM L (hdu.clm_apply (differentiableAt_const v)) w,
    ← fderiv_real_clm_apply hdu w v]

theorem mixedReal_comp_realCLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] ℝ) {u : ℂ → F} (hu : ContDiffAt ℝ 2 u 0) :
    mixedReal (fun p => L (u p)) = (1 / 4 : ℝ) * L
      (fderiv ℝ (fderiv ℝ u) 0 1 1 + fderiv ℝ (fderiv ℝ u) 0 Complex.I Complex.I) := by
  have hLu : ContDiffAt ℝ 2 (fun p => L (u p)) 0 := L.contDiff.comp_contDiffAt 0 hu
  rw [mixedReal, mixedWirt_real_diagonal hLu]
  simp only [smul_eq_mul, mul_one, secondFDeriv_comp_realCLM L hu, map_add]

end Yau.Blueprint.V03Proof
