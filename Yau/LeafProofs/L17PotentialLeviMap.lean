import Yau.LeafProofs.L17LocalHolderAlgebraBasic
import Yau.LeafProofs.L17ParabolicOperatorRegularity
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual complex Levi matrix is a bounded real linear image of the stored Hessian. -/

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux L17ParabolicOperatorAux

local instance leviMatrixTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)).toUniformSpace.toTopologicalSpace

def leviFromHessian {n : ℕ} (H : D2 n) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  ⟨(1/4 : ℝ)*(H (stdVec j) (stdVec i)+H (Complex.I • stdVec j) (Complex.I • stdVec i)),
    (1/4 : ℝ)*(H (stdVec j) (Complex.I • stdVec i)-H (Complex.I • stdVec j) (stdVec i))⟩

def leviHessianLinearMap (n : ℕ) : D2 n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := leviFromHessian
  map_add' H K := by
    ext i j
    apply Complex.ext <;> simp only [leviFromHessian,add_apply,Matrix.add_apply,Complex.add_re,Complex.add_im] <;> ring
  map_smul' c H := by
    ext i j
    apply Complex.ext <;>
      simp only [leviFromHessian, Matrix.smul_apply, RingHom.id_apply,
        smul_apply, smul_eq_mul, Complex.smul_re, Complex.smul_im] <;> ring

def leviHessianCLM (n : ℕ) : D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  { leviHessianLinearMap n with cont := (leviHessianLinearMap n).continuous_of_finiteDimensional }

theorem leviHessianCLM_apply {n : ℕ} (H : D2 n) : leviHessianCLM n H=leviFromHessian H := rfl

theorem leviC_eq_leviHessianCLM {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) : leviC f z=leviHessianCLM n (fderiv ℝ (fderiv ℝ f) z) := by
  ext i j
  apply Complex.ext
  · exact (L18Aux.leviMatrix_entry_re_im hf stdVec i j).1
  · exact (L18Aux.leviMatrix_entry_re_im hf stdVec i j).2

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def potentialLeviHolderCLM (P : UniformChartPartition g) (T γ : ℝ) (hT : 0 < T) :
    SchauderSpace P T γ hT →L[ℝ] LocalHolderSpace (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  (localMapCLM (leviHessianCLM n)).comp (hessianHolderCLM P T γ hT)

theorem potentialLeviHolderCLM_value (P : UniformChartPartition g) (T γ : ℝ) (hT : 0 < T)
    (u : SchauderSpace P T γ hT) (p : P.centers) (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    localFun _ (potentialLeviHolderCLM P T γ hT u) ⟨p,(z,t)⟩=leviC (chartFunction u p t) z := by
  change leviHessianCLM n (hessianFun u ⟨p,(z,t)⟩)=_
  rw [← (chartFunction_hasSecondFDerivAt u p t z.property).fderiv]
  exact (leviC_eq_leviHessianCLM ((chartFunction_contDiffOn_two u p t).contDiffAt
    (isOpen_ball.mem_nhds z.property))).symm

theorem potentialLeviHolderCLM_norm_le (P : UniformChartPartition g) (T γ : ℝ) (hT : 0 < T)
    (u : SchauderSpace P T γ hT) :
    ‖potentialLeviHolderCLM P T γ hT u‖ ≤ ‖leviHessianCLM n‖*‖u‖ := by
  exact (localMapElement_norm_le (leviHessianCLM n) _).trans
    (mul_le_mul_of_nonneg_left (hessianHolder_norm_le u) (norm_nonneg _))

end Yau.LeafProofs.L17Aux
