import Yau.Geometry.Polynomial

/-! Finite polynomial identities for the sharp exterior growth estimate. -/

open scoped Topology BigOperators

noncomputable section
namespace Yau.Blueprint.U03Proof

variable {n : ℕ}

theorem eval_comp (P Q : PolyMap n) (z : ComplexVector n) :
    (P.comp Q).eval z = P.eval (Q.eval z) := by
  ext i
  exact MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ) (fun j => z j) Q (P i)

theorem eval_id (z : ComplexVector n) :
    (PolyMap.id : PolyMap n).eval z = z := by
  ext i
  exact MvPolynomial.eval_X i

theorem inverse_eval_forward {P Q : PolyMap n}
    (h : IsPolyAutomorphism P Q) (z : ComplexVector n) :
    Q.eval (P.eval z) = z := by
  rw [← eval_comp, h.2, eval_id]

theorem support_weight_le {P : PolyMap n} {m : ℕ}
    (hPm : P.degree ≤ m) (i : Fin n) {β : Fin n →₀ ℕ}
    (hβ : β ∈ (P i).support) :
    β.sum (fun _ e => e) ≤ m := by
  have hc : (P i).totalDegree ≤ P.degree :=
    Finset.le_sup (f := fun j : Fin n => (P j).totalDegree) (Finset.mem_univ i)
  exact (MvPolynomial.le_totalDegree hβ).trans (hc.trans hPm)

def reflectedLine (P : PolyMap n) (m : ℕ)
    (v : ComplexVector n) (ζ : ℂ) : ComplexVector n :=
  WithLp.toLp 2 (fun i =>
    ∑ β ∈ (P i).support,
      (P i).coeff β * (∏ j, (v j) ^ (β j)) *
        ζ ^ (m - β.sum (fun _ e => e)))

theorem reflectedLine_differentiable (P : PolyMap n) (m : ℕ)
    (v : ComplexVector n) : Differentiable ℂ (reflectedLine P m v) := by
  apply (differentiable_piLp 2).2
  intro i
  change Differentiable ℂ (fun ζ : ℂ => ∑ β ∈ (P i).support,
    (P i).coeff β * (∏ j, (v j) ^ (β j)) * ζ ^ (m - β.sum (fun _ e => e)))
  apply Differentiable.fun_sum
  intro β _
  exact (differentiable_id.pow _).const_mul _

theorem reflectedLine_eq {P : PolyMap n} {m : ℕ}
    (hPm : P.degree ≤ m) (v : ComplexVector n) {ζ : ℂ}
    (hζ : ζ ≠ 0) :
    reflectedLine P m v ζ = ζ ^ m • P.eval (ζ⁻¹ • v) := by
  classical
  ext i
  change (∑ β ∈ (P i).support, (P i).coeff β * (∏ j, v j ^ β j) *
    ζ ^ (m - β.sum (fun _ e => e))) =
      ζ ^ m * MvPolynomial.eval (fun j => (ζ⁻¹ • v) j) (P i)
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  have hw := support_weight_le hPm i hβ
  have hsum : (∑ j, β j) = β.sum (fun _ e => e) := by
    symm
    exact Finsupp.sum_fintype _ _ (by simp)
  have hprod : (∏ j, (ζ⁻¹ • v) j ^ β j) =
      (ζ⁻¹) ^ (β.sum (fun _ e => e)) * ∏ j, v j ^ β j := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hsum]
  have hpow : ζ ^ m * (ζ⁻¹) ^ (β.sum (fun _ e => e)) =
      ζ ^ (m - β.sum (fun _ e => e)) := by
    simpa only [inv_pow] using (pow_sub₀ ζ hζ hw).symm
  rw [hprod]
  calc
    (P i).coeff β * (∏ j, v j ^ β j) * ζ ^ (m - β.sum (fun _ e => e)) =
        (P i).coeff β * (∏ j, v j ^ β j) *
          (ζ ^ m * (ζ⁻¹) ^ (β.sum (fun _ e => e))) := by rw [hpow]
    _ = _ := by ring

end Yau.Blueprint.U03Proof
