import Yau.Proofs.E02RealTensorLevi
import Yau.Proofs.E02EuclideanPacking

open Set Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

def envelopeSpaceSlice (n : ℕ) :
    (ComplexVector n × ComplexVector n) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).prod
    ((ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).prod 0)

def envelopeSpaceCoordinates (n : ℕ) :
    (ComplexVector n × ComplexVector n) →L[ℝ] EuclideanSpace ℝ (Fin (4*n+1)) :=
  (envelopeRealCoordinates n).toContinuousLinearMap.comp (envelopeSpaceSlice n)

def envelopeLowerPolynomial {n : ℕ} (c : ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ) (ε : ℝ) :
    ComplexVector n × ComplexVector n × ℝ → ℝ :=
  fun y => peanoLowerPolynomial c (envelopeRealCoordinates n a) p A ε (envelopeRealCoordinates n y)

theorem envelopeLowerPolynomial_contDiff {n : ℕ} (c : ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ) (ε : ℝ) :
    ContDiff ℝ ∞ (envelopeLowerPolynomial c a p A ε) :=
  (peanoLowerPolynomial_contDiff _ _ _ _ _).comp (envelopeRealCoordinates n).contDiff

/-- The attained-source lower test transports through the actual fixed
real chart, preserving the original source base and physical time. -/
theorem envelopeLowerPolynomial_source_test {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (v : EuclideanSpace ℝ (Fin (4*n+1)) → ℝ) (hv0 : ∀ y ∈ K, 0 ≤ v y)
    {κ : ℝ} (hκ : 0 < κ) (q : EuclideanSpace ℝ (Fin (4*n+1)))
    (a : ComplexVector n × ComplexVector n × ℝ)
    (ha : envelopeRealCoordinates n a ∈ interior K)
    (hMin : compactInfConvolution K v κ q = v (envelopeRealCoordinates n a)+
      ‖q-envelopeRealCoordinates n a‖^2/(2*κ))
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : RealSecondJet (compactInfConvolution K v κ) q p A)
    {ε : ℝ} (hε : 0 < ε) :
    envelopeLowerPolynomial (v (envelopeRealCoordinates n a)) a p A ε a =
        v (envelopeRealCoordinates n a) ∧
      ∀ᶠ y in 𝓝 a, envelopeLowerPolynomial (v (envelopeRealCoordinates n a)) a p A ε y ≤
        v (envelopeRealCoordinates n y) := by
  have h := compactInfConvolution_source_lower_test K v hv0 hκ q
    (envelopeRealCoordinates n a) ha hMin p A hJet hε
  refine ⟨h.2.1,?_⟩
  exact (envelopeRealCoordinates n).continuous.continuousAt.eventually h.2.2

/-- The genuine physical time derivative of the transported lower test
is exactly the original jet applied to the single packed time direction. -/
theorem envelopeLowerPolynomial_time_deriv {n : ℕ} (c : ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (ε : ℝ) :
    deriv (fun t => envelopeLowerPolynomial c a p A ε (a.1,a.2.1,t)) a.2.2 =
      p (envelopeRealCoordinates n (0,0,1)) := by
  have hPoly : HasFDerivAt (peanoLowerPolynomial c (envelopeRealCoordinates n a) p A ε)
      p (envelopeRealCoordinates n a) := by
    have hd := ((peanoLowerPolynomial_contDiff c (envelopeRealCoordinates n a) p A ε).differentiable
      (by simp) (envelopeRealCoordinates n a)).hasFDerivAt
    rwa [peanoLowerPolynomial_first_fderiv_at c _ p A hA ε] at hd
  have hPhi : HasFDerivAt (envelopeLowerPolynomial c a p A ε)
      (p.comp (envelopeRealCoordinates n).toContinuousLinearMap) a :=
    hPoly.comp a (envelopeRealCoordinates n).hasFDerivAt
  have hTime : HasDerivAt (fun t : ℝ => (a.1,a.2.1,t)) (0,0,1) a.2.2 := by
    simpa using (hasDerivAt_const a.2.2 a.1).prodMk
      ((hasDerivAt_const a.2.2 a.2.1).prodMk (hasDerivAt_id a.2.2))
  exact (hPhi.comp_hasDerivAt a.2.2 hTime).deriv

/-- Exact Levi matrix, with the real error 2ε retained before its
conversion to the complex ε-identity in the standard directions. -/
theorem envelopeLowerPolynomial_levi {n : ℕ} (c : ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (ε : ℝ) :
    leviMatrix (fun y : ComplexVector n × ComplexVector n =>
      envelopeLowerPolynomial c a p A ε (y.1,y.2,a.2.2)) (a.1,a.2.1) cotangentDir =
      realTensorLevi (A-(2*ε) • realInnerTensor)
        (fun i => envelopeSpaceCoordinates n (cotangentDir i))
        (fun i => envelopeSpaceCoordinates n (Complex.I • cotangentDir i)) := by
  have hArg (y : ComplexVector n × ComplexVector n) :
      envelopeRealCoordinates n (y.1,y.2,a.2.2) =
        envelopeRealCoordinates n (0,0,a.2.2)+envelopeSpaceCoordinates n y := by
    change envelopeRealCoordinates n (y.1,y.2,a.2.2) =
      envelopeRealCoordinates n (0,0,a.2.2)+envelopeRealCoordinates n (y.1,y.2,0)
    rw [←map_add]
    congr 1
    ext <;> simp [envelopeSpaceCoordinates,envelopeSpaceSlice]
  have hFun : (fun y : ComplexVector n × ComplexVector n =>
      envelopeLowerPolynomial c a p A ε (y.1,y.2,a.2.2)) =
      fun y => peanoLowerPolynomial c (envelopeRealCoordinates n a) p A ε
        (envelopeRealCoordinates n (0,0,a.2.2)+envelopeSpaceCoordinates n y) := by
    funext y
    exact congrArg (peanoLowerPolynomial c (envelopeRealCoordinates n a) p A ε) (hArg y)
  rw [hFun,leviMatrix_real_affine _ _
    ((peanoLowerPolynomial_contDiff c (envelopeRealCoordinates n a) p A ε).contDiffAt.of_le (by simp)),
    peanoLowerPolynomial_second_fderiv c _ p A hA ε]

end Yau.NodeProofs.E02Aux
