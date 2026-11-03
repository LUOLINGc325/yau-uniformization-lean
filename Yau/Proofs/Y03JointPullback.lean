import Yau.Proofs.Y03LeviQuadratic
import Yau.Proofs.Y03HolomorphicPullback

/-! The displayed joint cotangent/time Levi matrix controls the actual curve derivative. -/

open scoped ComplexOrder Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def jointDirection : Sum (Sum (Fin n) (Fin n)) Unit →
    ComplexVector n × ComplexVector n × ℂ :=
  Sum.elim (Sum.elim (fun i => (stdVec i, 0, 0)) (fun i => (0, stdVec i, 0)))
    (fun _ => (0, 0, 1))

def jointCoefficient (v : ComplexVector n × ComplexVector n × ℂ) :
    Sum (Sum (Fin n) (Fin n)) Unit → ℂ :=
  Sum.elim (Sum.elim (fun i => v.1 i) (fun i => v.2.1 i)) (fun _ => v.2.2)

theorem sum_stdVec (v : ComplexVector n) : ∑ i, v i • stdVec i = v := by
  ext j
  simp [stdVec, Pi.single_apply]

theorem jointDirection_span (v : ComplexVector n × ComplexVector n × ℂ) :
    ∑ i, jointCoefficient v i • jointDirection i = v := by
  simp only [jointCoefficient, jointDirection, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique, smul_eq_mul, Prod.smul_mk, smul_zero]
  simp only [mul_zero, mul_one, ← prod_mk_sum, Finset.sum_const_zero, sum_stdVec,
    Prod.mk_add_mk, zero_add, add_zero]

theorem jointPositiveClock_direction {X : KahlerManifold n} {h : Flow X}
    (hjoint : JointPositiveClock X h) (x : Pt X)
    (q : ComplexVector n × ComplexVector n × ℂ) (hq : q.1 ∈ chartTarget x)
    (hsmooth : ContDiffAt ℝ 2 (fun p : ComplexVector n × ComplexVector n × ℂ =>
      dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1) q)
    (v : ComplexVector n × ComplexVector n × ℂ) :
    0 ≤ (wirt (fun p => wirtBar (fun p : ComplexVector n × ComplexVector n × ℂ =>
      (dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1 : ℂ)) p v) q v).re := by
  have hp := hjoint x q.1 q.2.1 q.2.2 hq
  have hn := levi_direction_nonneg_of_posSemidef hsmooth jointDirection (jointCoefficient v) hp
  simpa only [jointDirection_span] using hn

theorem jointPositiveClock_holomorphic_pullback {X : KahlerManifold n} {h : Flow X}
    (hjoint : JointPositiveClock X h) (x : Pt X)
    (γ : ℂ → ComplexVector n × ComplexVector n × ℂ) (z : ℂ)
    (hγ : ContDiffAt ℂ 2 γ z) (hq : (γ z).1 ∈ chartTarget x)
    (hsmooth : ContDiffAt ℝ 2 (fun p : ComplexVector n × ComplexVector n × ℂ =>
      dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1) (γ z)) :
    0 ≤ (wirt (fun p => wirtBar (fun q : ℂ =>
      (dualNormChart (h (Real.exp (2 * (γ q).2.2.re))) x (γ q).1 (γ q).2.1 : ℂ)) p 1) z 1).re := by
  let f : ComplexVector n × ComplexVector n × ℂ → ℝ := fun p =>
    dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1
  have hfc : ContDiffAt ℝ 2 (Complex.ofRealCLM ∘ f) (γ z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hsmooth
  change 0 ≤ (wirt (fun p => wirtBar ((Complex.ofRealCLM ∘ f) ∘ γ) p 1) z 1).re
  rw [levi_direction_comp_holomorphic hfc hγ]
  exact jointPositiveClock_direction hjoint x (γ z) hq hsmooth (fderiv ℂ γ z 1)

end Yau.Blueprint.Alignment.Y03Proof
