import Yau.Proofs.Y01InverseJets
import Yau.Proofs.Y01SqrtEnvelopes

/-! Explicit closure of exp(C sqrt(s)) bounds under the finite polynomial
operations used in the primary coordinates and the bad-step jet. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem constant_le_sqrt_envelope {K s : ℝ} (hK : 0 ≤ K) (hs : 1 ≤ s) :
    K ≤ Real.exp (K * Real.sqrt s) := by
  have h := Real.add_one_le_exp K
  exact (show K ≤ Real.exp K by linarith).trans
    (Real.exp_le_exp.2 (le_mul_of_one_le_right hK (sqrt_one_le hs)))

theorem mul_sqrt_envelope {s A B x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ Real.exp (A * Real.sqrt s)) (hy : y ≤ Real.exp (B * Real.sqrt s)) :
    x * y ≤ Real.exp ((A + B) * Real.sqrt s) := by
  calc
    _ ≤ Real.exp (A * Real.sqrt s) * Real.exp (B * Real.sqrt s) :=
      mul_le_mul hx hy hy0 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pow_sqrt_envelope {s A x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ Real.exp (A * Real.sqrt s)) (m : ℕ) :
    x ^ m ≤ Real.exp (((m : ℝ) * A) * Real.sqrt s) := by
  calc
    _ ≤ Real.exp (A * Real.sqrt s) ^ m := pow_le_pow_left₀ hx0 hx m
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem one_add_sqrt_envelope {s A x : ℝ} (hs : 1 ≤ s)
    (hx : x ≤ Real.exp (A * Real.sqrt s)) :
    1 + x ≤ Real.exp ((max 0 A + Real.log 2) * Real.sqrt s) := by
  have h := exp_sqrt_add_bound (A := 0) hs
    (by simp : (1 : ℝ) ≤ Real.exp (0 * Real.sqrt s)) hx
  exact h

theorem jetComp_sqrt_envelope {s A B : ℝ} {d : ℕ} {P Q : PolyMap n}
    (hs : 1 ≤ s) (hdegree : P.degree ≤ d)
    (hP : P.coeffNorm ≤ Real.exp (A * Real.sqrt s))
    (hQ : Q.coeffNorm ≤ Real.exp (B * Real.sqrt s)) :
    (jetComp d P Q).coeffNorm ≤
      Real.exp ((A + (d : ℝ) * (max 0 B + Real.log 2)) * Real.sqrt s) := by
  have hbase : 1 ≤ 1 + Q.coeffNorm := by linarith [coeffNorm_nonneg Q]
  have hpow := pow_le_pow_right₀ hbase hdegree
  have hsum := one_add_sqrt_envelope hs hQ
  have hpowBound := pow_sqrt_envelope (by linarith [coeffNorm_nonneg Q]) hsum d
  exact (jetComp_coeffNorm d P Q).trans
    ((mul_le_mul_of_nonneg_left hpow (coeffNorm_nonneg P)).trans
      (mul_sqrt_envelope (coeffNorm_nonneg P) (by positivity) hP hpowBound))

theorem sqrt_step_bound {s t hm : ℝ} (hs : 0 ≤ s)
    (hstep : t - s ≤ (Real.exp hm - 1) * s) :
    Real.sqrt t ≤ Real.sqrt (Real.exp hm) * Real.sqrt s := by
  have ht : t ≤ Real.exp hm * s := by nlinarith
  have h := Real.sqrt_le_sqrt ht
  rwa [Real.sqrt_mul (Real.exp_pos hm).le] at h

theorem next_sqrt_envelope {s t hm A x : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hstep : t - s ≤ (Real.exp hm - 1) * s)
    (hx : x ≤ Real.exp (A * Real.sqrt t)) :
    x ≤ Real.exp ((A * Real.sqrt (Real.exp hm)) * Real.sqrt s) := by
  apply hx.trans (Real.exp_le_exp.2 _)
  have h := mul_le_mul_of_nonneg_left (sqrt_step_bound hs hstep) hA
  simpa only [mul_assoc] using h

end Yau.Proofs.Y01Aux
