import spec.CHAIN.CONTRACTS

/-! True time integration on the original closed interval. Only actual
one-sided derivatives are used; no integrability of a chosen derivative
field or extra endpoint regularity is assumed. -/
open Set
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem linear_upper_of_closed_derivative_cap {f d : ℝ → ℝ} {T a : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (d t) (Icc 0 T) t)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, d t ≤ a) :
    ∀ t ∈ Icc (0 : ℝ) T, f t ≤ f 0 + a * t := by
  let F : ℝ → ℝ := fun t => a * t - f t
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt F (a - d t) (Icc 0 T) t :=
    (hasDerivAt_const_mul (x := t) a).hasDerivWithinAt.sub (hf t ht)
  have hmono : MonotoneOn F (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (fun t ht => (hF t ht).continuousWithinAt)
      (fun t ht => (hF t (interior_subset ht)).mono interior_subset)
      (fun t ht => sub_nonneg.mpr (hd t (interior_subset ht)))
  intro t ht
  have h := hmono ⟨le_rfl, hT⟩ ht ht.1
  dsimp [F] at h
  linarith

theorem quadratic_upper_of_closed_derivative_cap {U P d : ℝ → ℝ} {T a : ℝ}
    (hT : 0 ≤ T) (hP0 : P 0 = 0)
    (hP : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt P (d t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt U (P t) (Icc 0 T) t)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, d t ≤ a) :
    ∀ t ∈ Icc (0 : ℝ) T, U t ≤ U 0 + a * t ^ 2 / 2 := by
  have hPupper (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : P t ≤ a * t := by
    simpa only [hP0, zero_add] using linear_upper_of_closed_derivative_cap hT hP hd t ht
  let F : ℝ → ℝ := fun t => a * t ^ 2 / 2 - U t
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt F (a * t - P t) (Icc 0 T) t := by
    have hq : HasDerivAt (fun s : ℝ => a * s ^ 2 / 2) (a * t) t := by
      have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hasDerivAt_pow 2 t
      convert (hpow.const_mul a).div_const 2 using 1 <;> ring
    exact hq.hasDerivWithinAt.sub (hU t ht)
  have hmono : MonotoneOn F (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (fun t ht => (hF t ht).continuousWithinAt)
      (fun t ht => (hF t (interior_subset ht)).mono interior_subset)
      (fun t ht => sub_nonneg.mpr (hPupper t (interior_subset ht)))
  intro t ht
  have h := hmono ⟨le_rfl, hT⟩ ht ht.1
  dsimp [F] at h
  nlinarith

theorem uniform_closed_time_potential_bounds {A : Type*} {U P d : A → ℝ → ℝ} {T a : ℝ}
    (hT : 0 ≤ T) (hP0 : ∀ x, P x 0 = 0) (hU0 : ∀ x, U x 0 = 0)
    (hP : ∀ x t, t ∈ Icc (0 : ℝ) T → HasDerivWithinAt (P x) (d x t) (Icc 0 T) t)
    (hU : ∀ x t, t ∈ Icc (0 : ℝ) T → HasDerivWithinAt (U x) (P x t) (Icc 0 T) t)
    (hd : ∀ x t, t ∈ Icc (0 : ℝ) T → d x t ≤ a) :
    ∀ x t, t ∈ Icc (0 : ℝ) T → P x t ≤ a * t ∧ U x t ≤ a * t ^ 2 / 2 := by
  intro x t ht
  constructor
  · simpa only [hP0, zero_add] using linear_upper_of_closed_derivative_cap hT (hP x) (hd x) t ht
  · simpa only [hU0, zero_add] using
      quadratic_upper_of_closed_derivative_cap hT (hP0 x) (hP x) (hU x) (hd x) t ht

theorem nonpositive_of_closed_nonpositive_derivative {f d : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hf0 : f 0 = 0)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (d t) (Icc 0 T) t)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, d t ≤ 0) : ∀ t ∈ Icc (0 : ℝ) T, f t ≤ 0 := by
  simpa only [hf0, zero_mul, zero_add] using linear_upper_of_closed_derivative_cap hT hf hd

end Yau.NodeProofs.F01Aux
