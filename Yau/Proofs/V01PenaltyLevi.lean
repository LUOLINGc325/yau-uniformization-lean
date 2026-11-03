import Yau.Proofs.V01SpatialSlice
import Yau.Proofs.V01FiniteGermSupport

noncomputable section
open scoped Topology ContDiff Matrix
namespace Yau.Blueprint.V01Proof
variable {n : ℕ}

/-- The computed spatial pullback of the true penalty tensor. -/
theorem normSquareTensor_spatial_apply (v w : CotangentCoord n) :
    normSquareTensor (spatialInjection v) (spatialInjection w) =
      2 * (inner ℝ v.1 w.1 + inner ℝ v.2 w.2) := by
  simp only [normSquareTensor_apply, spatialInjection_apply, zero_mul, add_zero]

/-- Real pairings of complex coordinate vectors retain the actual scalar
multipliers, including the imaginary directions in the Wirtinger formula. -/
theorem real_inner_smul_stdVec (a b : ℂ) (i j : Fin n) :
    inner ℝ (a • stdVec i) (b • stdVec j) =
      if i = j then (star a * b).re else 0 := by
  classical
  by_cases hij : i = j <;>
    simp [PiLp.inner_apply, stdVec, PiLp.single_apply,
      real_inner_eq_re_inner ℂ, apply_ite, hij, eq_comm, mul_comm]

theorem real_inner_stdVec (i j : Fin n) :
    inner ℝ (stdVec i) (stdVec j) = if i = j then 1 else 0 := by
  simpa using real_inner_smul_stdVec (1 : ℂ) 1 i j

theorem real_inner_I_stdVec_left (i j : Fin n) :
    inner ℝ (Complex.I • stdVec i) (stdVec j) = 0 := by
  simpa using real_inner_smul_stdVec Complex.I 1 i j

theorem real_inner_I_stdVec_right (i j : Fin n) :
    inner ℝ (stdVec i) (Complex.I • stdVec j) = 0 := by
  simpa using real_inner_smul_stdVec (1 : ℂ) Complex.I i j

theorem real_inner_I_stdVec_both (i j : Fin n) :
    inner ℝ (Complex.I • stdVec i) (Complex.I • stdVec j) =
      if i = j then 1 else 0 := by
  simpa using real_inner_smul_stdVec Complex.I Complex.I i j

/-- With the paper's quarter-Hessian convention, the sum-of-squares penalty
has exactly the identity spatial Levi matrix. -/
theorem realHessianLevi_normSquareTensor :
    realHessianLevi
      ((normSquareTensor (n := n)).bilinearComp spatialInjection spatialInjection)
      cotangentDir = (1 : CotangentMatrix n) := by
  ext i j
  change _ = if i = j then (1 : ℂ) else 0
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp only [realHessianLevi, ContinuousLinearMap.bilinearComp_apply,
      normSquareTensor_spatial_apply, cotangentDir, Sum.elim_inl, Sum.elim_inr,
      Prod.smul_fst, Prod.smul_snd, smul_zero, inner_zero_left, inner_zero_right,
      zero_add, add_zero, real_inner_stdVec, real_inner_I_stdVec_left,
      real_inner_I_stdVec_right, real_inner_I_stdVec_both]
    by_cases hij : i = j <;> norm_num [hij, eq_comm]

/-- A single globally quadratic test has its true constant spatial Levi matrix
at every receiving point, while its source jet is the finite C² germ. -/
theorem canonicalQuadraticSupport_spatialLevi
    {f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (a : ComplexVector n × ComplexVector n × ℝ) (hf : ContDiffAt ℝ 2 f a)
    (α : ℝ) (q : CotangentCoord n) (t : ℝ) :
    leviMatrix (fun z : CotangentCoord n =>
      canonicalQuadraticSupport f a α (z.1, z.2, t)) q cotangentDir =
      leviMatrix (fun z : CotangentCoord n => f (z.1, z.2, a.2.2))
        (a.1, a.2.1) cotangentDir - (α : ℂ) • (1 : CotangentMatrix n) := by
  have hψ : ContDiffAt ℝ 2 (canonicalQuadraticSupport f a α) (spatialAffine t q) :=
    (canonicalQuadraticSupport_contDiff f a α).contDiffAt.of_le (by norm_num)
  have hψSlice : ContDiffAt ℝ 2 (fun z : CotangentCoord n =>
      canonicalQuadraticSupport f a α (z.1, z.2, t)) q :=
    hψ.comp q ((spatialAffine_contDiff t).contDiffAt.of_le (by norm_num))
  have hfSlice : ContDiffAt ℝ 2 (fun z : CotangentCoord n => f (z.1, z.2, a.2.2))
      (a.1, a.2.1) :=
    hf.comp (a.1, a.2.1) ((spatialAffine_contDiff a.2.2).contDiffAt.of_le (by norm_num))
  rw [leviMatrix_eq_realHessianLevi hψSlice, leviMatrix_eq_realHessianLevi hfSlice,
    second_fderiv_spatialSlice t q hψ,
    second_fderiv_spatialSlice a.2.2 (a.1, a.2.1) hf]
  change realHessianLevi
    ((fderiv ℝ (fderiv ℝ (quadraticSupport f a (fderiv ℝ f a)
      (fderiv ℝ (fderiv ℝ f) a) α)) (spatialAffine t q)).bilinearComp
        spatialInjection spatialInjection) cotangentDir = _
  rw [quadraticSupport_second_fderiv f a _ _
    (Yau.NodeProofs.E02Aux.realSecondJet_of_contDiffAt_two hf).1 α]
  have hb : ((fderiv ℝ (fderiv ℝ f) a - α • normSquareTensor).bilinearComp
      spatialInjection spatialInjection) =
      (fderiv ℝ (fderiv ℝ f) a).bilinearComp spatialInjection spatialInjection -
      α • ((normSquareTensor (n := n)).bilinearComp spatialInjection spatialInjection) := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply, smul_apply]
  rw [hb, realHessianLevi_sub, realHessianLevi_real_smul,
    realHessianLevi_normSquareTensor]
  rfl

end Yau.Blueprint.V01Proof
