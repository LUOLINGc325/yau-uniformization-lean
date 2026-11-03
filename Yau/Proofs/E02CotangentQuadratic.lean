import Yau.Proofs.E02EnvelopeTestTransport

open Matrix
open scoped Topology ContDiff InnerProductSpace Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

theorem envelopeSpaceCoordinates_norm_sq {n : ℕ} (q : ComplexVector n × ComplexVector n) :
    ‖envelopeSpaceCoordinates n q‖^2 = ‖q.1‖^2+‖q.2‖^2 := by
  simpa [envelopeSpaceCoordinates,envelopeSpaceSlice] using
    envelopeRealCoordinates_norm_sq n (q.1,q.2,0)

/-- The actual packed spatial slice has the sum inner product even
though the topology-bearing ordinary complex product has a max norm. -/
theorem envelopeSpaceCoordinates_inner {n : ℕ} (q r : ComplexVector n × ComplexVector n) :
    ⟪envelopeSpaceCoordinates n q,envelopeSpaceCoordinates n r⟫_ℝ =
      ⟪q.1,r.1⟫_ℝ+⟪q.2,r.2⟫_ℝ := by
  have h := envelopeSpaceCoordinates_norm_sq (q+r)
  rw [map_add,norm_add_sq_real,envelopeSpaceCoordinates_norm_sq,
    envelopeSpaceCoordinates_norm_sq] at h
  simp only [Prod.fst_add,Prod.snd_add,norm_add_sq_real] at h
  linarith

theorem complexVector_real_inner {n : ℕ} (v w : ComplexVector n) :
    ⟪v,w⟫_ℝ = (⟪v,w⟫_ℂ).re := by
  simp only [PiLp.inner_apply,Complex.inner,RCLike.inner_apply]
  simpa using (map_sum Complex.reCLM (fun i : Fin n => w i*star (v i)) Finset.univ).symm

/-- Exact half-identity for the real inner tensor in the original
cotangent directions. This fixes the real2ε-to-complexε normalization. -/
theorem realTensorLevi_packed_inner (n : ℕ) :
    realTensorLevi (realInnerTensor (E := EuclideanSpace ℝ (Fin (4*n+1))))
      (fun i => envelopeSpaceCoordinates n (cotangentDir i))
      (fun i => envelopeSpaceCoordinates n (Complex.I • cotangentDir i)) =
      (1/2 : ℂ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
  have hEval (v w : EuclideanSpace ℝ (Fin (4*n+1))) :
      realInnerTensor v w = ⟪v,w⟫_ℝ := rfl
  apply Matrix.ext
  intro i j
  apply Complex.ext <;>
    simp only [realTensorLevi,hEval,envelopeSpaceCoordinates_inner,
      Matrix.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im]
  all_goals
    rcases i with i|i <;> rcases j with j|j
  all_goals
    by_cases hij : i=j
    · subst j
      simp [cotangentDir,complexVector_real_inner,inner_smul_left,inner_smul_right,
        stdVec,EuclideanSpace.inner_single_left,Matrix.one_apply,norm_smul] <;> norm_num
    · simp [cotangentDir,complexVector_real_inner,inner_smul_left,inner_smul_right,
        stdVec,EuclideanSpace.inner_single_left,Matrix.one_apply,hij,Ne.symm hij]

/-- The actual nested Levi of the translated polynomial loses exactly
εI. The Peano tensor remains a given tensor, never a derivative of uκ. -/
theorem envelopeLowerPolynomial_levi_sub_epsilon {n : ℕ} (c : ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (ε : ℝ) :
    leviMatrix (fun y : ComplexVector n × ComplexVector n =>
      envelopeLowerPolynomial c a p A ε (y.1,y.2,a.2.2)) (a.1,a.2.1) cotangentDir =
      realTensorLevi A
        (fun i => envelopeSpaceCoordinates n (cotangentDir i))
        (fun i => envelopeSpaceCoordinates n (Complex.I • cotangentDir i))-
        (ε : ℂ) • 1 := by
  rw [envelopeLowerPolynomial_levi c a p A hA ε,realTensorLevi_sub_smul,
    realTensorLevi_packed_inner,smul_smul]
  have hScalar : ((2*ε : ℝ) : ℂ)*(1/2 : ℂ) = (ε : ℂ) := by push_cast; ring
  rw [hScalar]

end Yau.NodeProofs.E02Aux
