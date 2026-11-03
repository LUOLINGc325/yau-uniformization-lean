import Yau.Proofs.V01QuadraticSupport

/-! V01 scratch source: the quadratic lower support keeps the ordinary
physical-time derivative at the original contact point. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

open Yau.NodeProofs.E02Aux

variable {n : ℕ}

theorem coordinateSquare_time_hasDerivAt
    (a : ComplexVector n × ComplexVector n × ℝ) :
    HasDerivAt (fun t => coordinateSquare a (a.1, a.2.1, t)) 0 a.2.2 := by
  convert (((hasDerivAt_id a.2.2).sub_const a.2.2).pow 2) using 1 <;>
    simp [coordinateSquare] <;> rfl

theorem quadraticSupport_time_hasDerivAt
    (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ)
    (p : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (α : ℝ) :
    HasDerivAt (fun t => quadraticSupport f a p A α (a.1, a.2.1, t))
      (p (0, 0, 1)) a.2.2 := by
  have hline : HasDerivAt (fun t : ℝ => (a.1, a.2.1, t))
      (0, 0, 1) a.2.2 :=
    (hasDerivAt_const a.2.2 a.1).prodMk
      ((hasDerivAt_const a.2.2 a.2.1).prodMk (hasDerivAt_id a.2.2))
  have hpoly : HasFDerivAt (jetPolynomial (f a) a p A) p a := by
    simpa using jetPolynomial_hasFDerivAt (f a) a p A hA a
  have hpolytime := hpoly.comp_hasDerivAt a.2.2 (by simpa using hline)
  have hpenalty := (coordinateSquare_time_hasDerivAt a).const_mul α
  convert hpolytime.sub hpenalty using 1 <;>
    simp [quadraticSupport, Function.comp_def] <;> rfl

theorem quadraticSupport_time_deriv_eq
    {f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ComplexVector n × ℝ}
    (hf : DifferentiableAt ℝ f a)
    (A : (ComplexVector n × ComplexVector n × ℝ) →L[ℝ]
      (ComplexVector n × ComplexVector n × ℝ) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (α : ℝ) :
    deriv (fun t => quadraticSupport f a (fderiv ℝ f a) A α (a.1, a.2.1, t)) a.2.2 =
      deriv (fun t => f (a.1, a.2.1, t)) a.2.2 := by
  have hline : HasDerivAt (fun t : ℝ => (a.1, a.2.1, t))
      (0, 0, 1) a.2.2 :=
    (hasDerivAt_const a.2.2 a.1).prodMk
      ((hasDerivAt_const a.2.2 a.2.1).prodMk (hasDerivAt_id a.2.2))
  rw [(quadraticSupport_time_hasDerivAt f a (fderiv ℝ f a) A hA α).deriv]
  have hft : HasDerivAt (fun t => f (a.1, a.2.1, t))
      (fderiv ℝ f a (0, 0, 1)) a.2.2 := by
    simpa only [Function.comp_def] using
      (hf.hasFDerivAt.comp_hasDerivAt a.2.2 (by simpa using hline))
  exact hft.deriv.symm

end Yau.Blueprint.V01Proof
