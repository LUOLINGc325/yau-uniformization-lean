import Yau.Proofs.C02ConnectionCurvature

/-! The radial homotopy formula derived from the computed curvature of a
smooth radial-gauge connection. Both its sign and weight are explicit. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance radial_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance radial_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance radial_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance radial_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance radial_two_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance radial_two_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem radial_connection_differentiated (A : E → E →L[ℝ] E →L[ℝ] E)
    (hRad : ∀ y, A y y = 0) {y : E} (hA : DifferentiableAt ℝ A y) (u : E) :
    fderiv ℝ A y u y + A y u = 0 := by
  have hd := hA.hasFDerivAt.clm_apply (hasFDerivAt_id y)
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L u) hd.fderiv
  have hz : (fun z => A z z) = (fun _ : E => (0 : E →L[ℝ] E)) := funext hRad
  change (fderiv ℝ (fun z => A z z) y) u = A y u + fderiv ℝ A y u y at he
  have hzero : fderiv ℝ (fun _ : E => (0 : E →L[ℝ] E)) y = 0 :=
    (hasFDerivAt_const (0 : E →L[ℝ] E) y).fderiv
  rw [hz, hzero] at he
  simpa only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, add_comm] using he.symm

theorem radial_connection_integrand (A : E → E →L[ℝ] E →L[ℝ] E)
    (hA : Differentiable ℝ A) (hRad : ∀ y, A y y = 0) (t : ℝ) (x : E) :
    t • connectionCurvature A (t • x) x = A (t • x) + t • fderiv ℝ A (t • x) x := by
  have hAx : t • A (t • x) x = 0 := by simpa only [map_smul] using hRad (t • x)
  apply ContinuousLinearMap.ext
  intro u
  have hd := radial_connection_differentiated A hRad (hA (t • x)) u
  rw [map_smul] at hd
  have hd' : t • fderiv ℝ A (t • x) u x = -A (t • x) u := eq_neg_of_add_eq_zero_left hd
  have hC1 : t • ((A (t • x) x).comp (A (t • x) u)) = 0 := by
    apply ContinuousLinearMap.ext
    intro z
    change (t • A (t • x) x) (A (t • x) u z) = 0
    rw [hAx]
    rfl
  have hC2 : t • ((A (t • x) u).comp (A (t • x) x)) = 0 := by
    apply ContinuousLinearMap.ext
    intro z
    have hp : t • A (t • x) x z = 0 := congrArg (fun L : E →L[ℝ] E => L z) hAx
    change t • A (t • x) u (A (t • x) x z) = 0
    rw [← (A (t • x) u).map_smul, hp, map_zero]
  change t • connectionCurvature A (t • x) x u = A (t • x) u + t • fderiv ℝ A (t • x) x u
  rw [connectionCurvature_apply, smul_sub, smul_add, smul_sub, hd', hC1, hC2]
  abel

theorem radial_connection_homotopy [CompleteSpace E] [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (hRad : ∀ y, A y y = 0) (x : E) :
    radialHomotopy (connectionCurvature A) x = A x := by
  have hD : Differentiable ℝ A := hA.differentiable (by simp)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • A (s • x))
      (t • connectionCurvature A (t • x) x) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x
    have hcurve : HasDerivAt (fun s : ℝ => A (s • x)) (fderiv ℝ A (t • x) x) t := by
      simpa only [Function.comp_def] using (hD (t • x)).hasFDerivAt.comp_hasDerivAt t hline
    rw [radial_connection_integrand A hD hRad t x]
    convert (hasDerivAt_id t).smul hcurve using 1 <;>
      first | rfl | simp only [id_eq, one_smul, add_comm]
  have hint : IntervalIntegrable (fun t : ℝ => t • connectionCurvature A (t • x) x) volume 0 1 :=
    (continuous_id.smul (((connectionCurvature_smooth A hA).continuous.comp
      (continuous_id.smul continuous_const)).clm_apply continuous_const)).intervalIntegrable 0 1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t) hint
  simpa only [radialHomotopy, one_smul, zero_smul, sub_zero] using hi

end Yau.Blueprint.C02Proof
