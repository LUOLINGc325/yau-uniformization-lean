import Yau.Proofs.E02PeanoJet

open Set Filter Asymptotics
open scoped Topology ContDiff Asymptotics
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual quadratic polynomial attached to a symmetric bilinear tensor. -/
def jetPolynomial (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (y : E) : ℝ :=
  c+p (y-a)+(1/2)*A (y-a) (y-a)

theorem jetPolynomial_contDiff (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) : ContDiff ℝ ∞ (jetPolynomial c a p A) := by
  unfold jetPolynomial
  fun_prop

theorem jetPolynomial_hasFDerivAt (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ v w, A v w = A w v) (x : E) :
    HasFDerivAt (jetPolynomial c a p A) (p+A (x-a)) x := by
  have hd : HasFDerivAt (fun y : E => y-a) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const a
  have hl := p.hasFDerivAt.comp x hd
  have hq := A.hasFDerivAt_of_bilinear hd hd
  convert ((hasFDerivAt_const c x).add hl).add (hq.const_mul (1/2)) using 1
  · rfl
  · ext v
    change p v+A (x-a) v = 0+p v+(1/2)*(A (x-a) v+A v (x-a))
    rw [hA v (x-a)]
    ring

/-- This is the genuine second Frechet derivative of the polynomial.
No such identification is made for a merely Peano differentiable function. -/
theorem jetPolynomial_second_fderiv (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ v w, A v w = A w v) (x : E) :
    fderiv ℝ (fderiv ℝ (jetPolynomial c a p A)) x = A := by
  have hF : fderiv ℝ (jetPolynomial c a p A) = fun y => p+A (y-a) := by
    funext y
    exact (jetPolynomial_hasFDerivAt c a p A hA y).fderiv
  rw [hF]
  have hd := A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using (hd.const_add p).fderiv

theorem jetPolynomial_realSecondJet (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ v w, A v w = A w v) :
    RealSecondJet (jetPolynomial c a p A) a p A := by
  refine ⟨hA,?_⟩
  have hZero : (fun y => jetPolynomial c a p A y-jetPolynomial c a p A a-
      p (y-a)-(1/2)*A (y-a) (y-a)) = fun _ => 0 := by
    funext y
    simp [jetPolynomial]
    ring
  rw [hZero]
  exact isLittleO_zero _ _

end Yau.NodeProofs.E02Aux
