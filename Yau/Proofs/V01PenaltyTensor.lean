import Yau.Proofs.V01QuadraticSupport
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! V01 scratch source: the sum-of-squares penalty is itself an actual
quadratic polynomial with a computed symmetric real tensor. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

open Yau.NodeProofs.E02Aux
variable {n : ℕ}

def contactFirstCLM : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ComplexVector n :=
  ContinuousLinearMap.fst ℝ _ _

def contactSecondCLM : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ComplexVector n :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def contactTimeCLM : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def contactInnerTensor
    (L : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ComplexVector n) :
    (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ).bilinearComp L L

def contactTimeTensor : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
    (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (contactTimeCLM (n := n)) (contactTimeCLM (n := n))

def sumQuadraticTensors {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • (A + B + C)

theorem sumQuadraticTensors_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    sumQuadraticTensors A B C v w = 2 * (A v w + B v w + C v w) := by
  simp only [sumQuadraticTensors, smul_apply, add_apply, smul_eq_mul]

def normSquareTensor : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
    (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ :=
  sumQuadraticTensors (contactInnerTensor (n := n) contactFirstCLM)
    (contactInnerTensor (n := n) contactSecondCLM) (contactTimeTensor (n := n))

theorem normSquareTensor_apply (v w : ComplexVector n × ComplexVector n × ℝ) :
    normSquareTensor v w =
      2 * (inner ℝ v.1 w.1 + inner ℝ v.2.1 w.2.1 + v.2.2 * w.2.2) := by
  change sumQuadraticTensors _ _ _ v w = _
  rw [sumQuadraticTensors_apply]
  rfl

theorem normSquareTensor_symmetric (v w : ComplexVector n × ComplexVector n × ℝ) :
    normSquareTensor v w = normSquareTensor w v := by
  rw [normSquareTensor_apply, normSquareTensor_apply,
    real_inner_comm v.1 w.1, real_inner_comm v.2.1 w.2.1]
  ring

theorem normSquareTensor_jetPolynomial
    (a y : ComplexVector n × ComplexVector n × ℝ) :
    jetPolynomial 0 a 0 normSquareTensor y = coordinateSquare a y := by
  simp only [jetPolynomial, zero_add, zero_apply, normSquareTensor_apply,
    Prod.fst_sub, Prod.snd_sub, real_inner_self_eq_norm_sq, coordinateSquare]
  ring

theorem quadraticSupport_eq_jetPolynomial
    (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ) (α : ℝ) :
    quadraticSupport f a p A α = jetPolynomial (f a) a p (A - α • normSquareTensor) := by
  funext y
  unfold quadraticSupport
  rw [← normSquareTensor_jetPolynomial a y]
  simp only [jetPolynomial, sub_apply, smul_apply,
    smul_eq_mul, zero_apply, zero_add]
  ring

theorem quadraticSupport_second_fderiv
    (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (α : ℝ)
    (y : ComplexVector n × ComplexVector n × ℝ) :
    fderiv ℝ (fderiv ℝ (quadraticSupport f a p A α)) y = A - α • normSquareTensor := by
  rw [quadraticSupport_eq_jetPolynomial]
  apply jetPolynomial_second_fderiv
  intro v w
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [hA v w, normSquareTensor_symmetric v w]

end Yau.Blueprint.V01Proof
