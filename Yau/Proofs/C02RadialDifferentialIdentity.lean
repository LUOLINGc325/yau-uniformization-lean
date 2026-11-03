import Yau.Proofs.C02RadialConnectionIdentity

/-! The second radial homotopy formula, derived from torsion freeness and
the exact radial identities. It does not assume any differential bound. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance differential_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance differential_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance differential_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance differential_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem radial_linear_differentiated (B : E → E →L[ℝ] E)
    (hRad : ∀ y, B y y = y) {y : E} (hB : DifferentiableAt ℝ B y) (u : E) :
    fderiv ℝ B y u y + B y u = u := by
  have hd := hB.hasFDerivAt.clm_apply (hasFDerivAt_id y)
  have he := congrArg (fun L : E →L[ℝ] E => L u) hd.fderiv
  have hz : (fun z => B z z) = id := funext hRad
  change (fderiv ℝ (fun z => B z z) y) u = B y u + fderiv ℝ B y u y at he
  rw [hz, fderiv_id] at he
  simpa only [ContinuousLinearMap.id_apply, add_comm] using he.symm

theorem radial_differential_integrand (A : E → E →L[ℝ] E →L[ℝ] E) (B : E → E →L[ℝ] E)
    (hB : Differentiable ℝ B) (hRadA : ∀ y, A y y = 0) (hRadB : ∀ y, B y y = y)
    (hTor : ∀ y u v, fderiv ℝ B y u v - fderiv ℝ B y v u +
      A y u (B y v) - A y v (B y u) = 0) (t : ℝ) (x : E) :
    B (t • x) + t • fderiv ℝ B (t • x) x =
      ContinuousLinearMap.id ℝ E + t • (A (t • x)).flip x := by
  apply ContinuousLinearMap.ext
  intro u
  have hd := radial_linear_differentiated B hRadB (hB (t • x)) u
  rw [map_smul] at hd
  have hAx : t • A (t • x) x = 0 := by simpa only [map_smul] using hRadA (t • x)
  have hC1 : t • A (t • x) x (B (t • x) u) = 0 :=
    congrArg (fun L : E →L[ℝ] E => L (B (t • x) u)) hAx
  have hC2 : t • A (t • x) u (B (t • x) x) = t • A (t • x) u x := by
    calc
      _ = A (t • x) u (t • B (t • x) x) := ((A (t • x) u).map_smul t _).symm
      _ = A (t • x) u (B (t • x) (t • x)) := by rw [(B (t • x)).map_smul]
      _ = A (t • x) u (t • x) := by rw [hRadB]
      _ = _ := (A (t • x) u).map_smul t x
  have ht := congrArg (fun v : E => t • v) (hTor (t • x) x u)
  rw [smul_sub, smul_add, smul_sub, hC1, hC2, smul_zero, add_zero] at ht
  change B (t • x) u + t • fderiv ℝ B (t • x) x u = u + t • A (t • x) u x
  calc
    _ = (t • fderiv ℝ B (t • x) x u - t • fderiv ℝ B (t • x) u x - t • A (t • x) u x) +
        (t • fderiv ℝ B (t • x) u x + B (t • x) u) + t • A (t • x) u x := by abel
    _ = _ := by rw [ht, hd]; simp only [zero_add]

theorem radial_differential_homotopy [CompleteSpace E] [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E →L[ℝ] E) (B : E → E →L[ℝ] E)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hRadA : ∀ y, A y y = 0) (hRadB : ∀ y, B y y = y)
    (hTor : ∀ y u v, fderiv ℝ B y u v - fderiv ℝ B y v u +
      A y u (B y v) - A y v (B y u) = 0) (x : E) :
    B x = ContinuousLinearMap.id ℝ E + radialHomotopy (fun y => (A y).flip) x := by
  have hBD : Differentiable ℝ B := hB.differentiable (by simp)
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => s • (B (s • x) - ContinuousLinearMap.id ℝ E))
      (t • (A (t • x)).flip x) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x
    have hcurve : HasDerivAt (fun s : ℝ => B (s • x)) (fderiv ℝ B (t • x) x) t := by
      simpa only [Function.comp_def] using (hBD (t • x)).hasFDerivAt.comp_hasDerivAt t hline
    have hd := (hasDerivAt_id t).smul (hcurve.sub_const (ContinuousLinearMap.id ℝ E))
    have heq : t • (A (t • x)).flip x = B (t • x) - ContinuousLinearMap.id ℝ E +
        t • fderiv ℝ B (t • x) x := by
      have hi := radial_differential_integrand A B hBD hRadA hRadB hTor t x
      calc
        _ = (ContinuousLinearMap.id ℝ E + t • (A (t • x)).flip x) - ContinuousLinearMap.id ℝ E := by abel
        _ = _ := by rw [← hi]; abel
    rw [heq]
    convert hd using 1 <;> first | rfl | simp only [id_eq, one_smul, add_comm]
  have hAf : Continuous (fun y => (A y).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp hA.continuous
  have hint : IntervalIntegrable (fun t : ℝ => t • (A (t • x)).flip x) volume 0 1 :=
    (continuous_id.smul ((hAf.comp (continuous_id.smul continuous_const)).clm_apply
      continuous_const)).intervalIntegrable 0 1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t) hint
  have hH : radialHomotopy (fun y => (A y).flip) x = B x - ContinuousLinearMap.id ℝ E := by
    simpa only [radialHomotopy, one_smul, zero_smul, sub_zero] using hi
  rw [hH]
  abel

end Yau.Blueprint.C02Proof
