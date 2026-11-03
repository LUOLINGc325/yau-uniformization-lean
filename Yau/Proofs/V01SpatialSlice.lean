import Yau.Proofs.V01LeviJet
import Yau.Proofs.V01PenaltyTensor

/-! V01 scratch source: the right-associated space-time input is restricted
through one explicit affine spatial slice with its genuine derivative. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

def spatialInjection : CotangentCoord n →L[ℝ]
    (ComplexVector n × ComplexVector n × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).prod
    ((ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).prod 0)

@[simp] theorem spatialInjection_apply (v : CotangentCoord n) :
    spatialInjection v = (v.1, v.2, 0) := rfl

def spatialAffine (t : ℝ) (q : CotangentCoord n) :
    ComplexVector n × ComplexVector n × ℝ := (q.1, q.2, t)

theorem spatialAffine_contDiff (t : ℝ) : ContDiff ℝ ∞ (spatialAffine (n := n) t) := by
  unfold spatialAffine
  fun_prop

theorem spatialAffine_hasFDerivAt (t : ℝ) (q : CotangentCoord n) :
    HasFDerivAt (spatialAffine t) spatialInjection q := by
  convert spatialInjection.hasFDerivAt.add_const (0, 0, t) using 1
  funext u
  simp [spatialAffine, spatialInjection_apply]

@[simp] theorem spatialAffine_fderiv (t : ℝ) (q : CotangentCoord n) :
    fderiv ℝ (spatialAffine t) q = spatialInjection :=
  (spatialAffine_hasFDerivAt t q).fderiv

@[simp] theorem spatialAffine_second_fderiv (t : ℝ) (q : CotangentCoord n) :
    fderiv ℝ (fderiv ℝ (spatialAffine t)) q = 0 := by
  have heq : fderiv ℝ (spatialAffine (n := n) t) = fun _ => spatialInjection :=
    funext (spatialAffine_fderiv t)
  rw [heq]
  exact (hasFDerivAt_const spatialInjection q).fderiv

theorem second_fderiv_spatialSlice
    {f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (t : ℝ) (q : CotangentCoord n) (hf : ContDiffAt ℝ 2 f (spatialAffine t q)) :
    fderiv ℝ (fderiv ℝ (fun z : CotangentCoord n => f (z.1, z.2, t))) q =
      (fderiv ℝ (fderiv ℝ f) (spatialAffine t q)).bilinearComp spatialInjection spatialInjection := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have h := Yau.Blueprint.V03Proof.secondFDeriv_comp
    ((spatialAffine_contDiff t).contDiffAt.of_le (by norm_num)) hf v w
  simpa only [Function.comp_def, spatialAffine, spatialAffine_fderiv,
    spatialAffine_second_fderiv, zero_apply, map_zero, add_zero,
    ContinuousLinearMap.bilinearComp_apply] using h

end Yau.Blueprint.V01Proof
