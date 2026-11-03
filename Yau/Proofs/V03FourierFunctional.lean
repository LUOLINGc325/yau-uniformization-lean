import Yau.Proofs.V03FourierRapidDecay

/-! Each native Fourier coefficient is a bounded complex-linear functional
on continuous circle traces, with its exact integral definition. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

def fourierCoeffFunctional (k : ℤ) : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => fourierCoeff (f : AddCircle T → ℂ) k
      map_add' := by
        intro f g
        have hh := congrArg (fun v : ℤ → ℂ => v k)
          (fourierCoeff.add
            (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))
        simpa only [ContinuousMap.coe_add, Pi.add_apply] using hh
      map_smul' := by
        intro c f
        simpa only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply] using
          fourierCoeff.const_smul (f : AddCircle T → ℂ) c k }
    1 (fun f => by
      change ‖fourierCoeff (f : AddCircle T → ℂ) k‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using fourierCoeff_norm_le_bound (fun x => f.norm_coe_le_norm x) k)

theorem fourierCoeffFunctional_apply (k : ℤ) (f : C(AddCircle T, ℂ)) :
    fourierCoeffFunctional k f = fourierCoeff (f : AddCircle T → ℂ) k := rfl

theorem fourierCoeffFunctional_norm_le (k : ℤ) : ‖fourierCoeffFunctional (T := T) k‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le
  exact zero_le_one

end Yau.Blueprint.V03Proof
