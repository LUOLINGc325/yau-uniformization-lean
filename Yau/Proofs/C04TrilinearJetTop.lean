import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Uniform top-coefficient extraction for a fixed trilinear map. -/

namespace Yau.Proofs.C04Aux.TrilinearJetTopAux

open scoped BigOperators ContDiff

set_option maxSynthPendingDepth 5

/-- A finite constant depending only on the derivative order. -/
def leibnizConstant (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (i + 1),
    (m.choose i : ℝ) * (i.choose j : ℝ)

theorem leibnizConstant_nonneg (m : ℕ) : 0 ≤ leibnizConstant m := by
  unfold leibnizConstant
  positivity

/-- The two possible top-order derivatives of the repeated factor have coefficient one. -/
theorem double_sum_top_two {m : ℕ} (_hm : 1 ≤ m)
    (F A : ℕ → ℝ) (hF0 : ∀ j, 0 ≤ F j) (hA0 : ∀ j, 0 ≤ A j)
    {B0 α U L : ℝ} (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hf0 : F 0 ≤ B0) (ha0 : A 0 ≤ α)
    (hf : ∀ j, j ≤ m → F j ≤ U) (ha : ∀ j, j < m → A j ≤ L) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (i + 1),
      (m.choose i : ℝ) * (i.choose j : ℝ) * F j * A (i - j) * A (m - i)) ≤
      2 * B0 * α * A m + leibnizConstant m * U * L ^ 2 := by
  have hB0 : 0 ≤ B0 := (hF0 0).trans hf0
  have hα : 0 ≤ α := (hA0 0).trans ha0
  let K := B0 * α * A m
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hB0 hα) (hA0 m)
  have hterm : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (i + 1),
      (m.choose i : ℝ) * (i.choose j : ℝ) * F j * A (i-j) * A (m-i) ≤
      (m.choose i : ℝ) * (i.choose j : ℝ) * U * L ^ 2 +
        (if i = 0 ∧ j = 0 then K else 0) + (if i = m ∧ j = 0 then K else 0) := by
    intro i hi j hj
    have hi' : i ≤ m := by simpa using Finset.mem_range.mp hi
    have hj' : j ≤ i := by simpa using Finset.mem_range.mp hj
    by_cases hfirst : i = 0 ∧ j = 0
    · rcases hfirst with ⟨rfl, rfl⟩
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_self,
        Nat.sub_zero, and_self, ↓reduceIte]
      have htop : F 0 * A 0 * A m ≤ K := by
        dsimp [K]
        gcongr <;> exact hA0 _
      have hlow : 0 ≤ U * L ^ 2 := by positivity
      split_ifs <;> nlinarith
    by_cases hlast : i = m ∧ j = 0
    · rcases hlast with ⟨hi_eq, hj_eq⟩
      subst i
      subst j
      simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_mul,
        Nat.sub_zero, Nat.sub_self, and_self, ↓reduceIte]
      have htop : F 0 * A m * A 0 ≤ K := by
        dsimp [K]
        calc
          F 0 * A m * A 0 = F 0 * A 0 * A m := by ring
          _ ≤ B0 * α * A m := by gcongr <;> exact hA0 _
      have hlow : 0 ≤ U * L ^ 2 := by positivity
      split_ifs <;> nlinarith
    have hleft : i - j < m := by
      by_contra hn
      have : i = m ∧ j = 0 := by omega
      exact hlast this
    have hright : m - i < m := by
      by_contra hn
      have : i = 0 ∧ j = 0 := by omega
      exact hfirst this
    simp only [hfirst, hlast, ↓reduceIte, add_zero]
    calc
      _ ≤ (m.choose i : ℝ) * (i.choose j : ℝ) * U * L * L := by
        gcongr <;> first | exact hA0 _ | exact hf j (hj'.trans hi') |
          exact ha (i-j) hleft | exact ha (m-i) hright
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (i+1),
        ((m.choose i : ℝ) * (i.choose j : ℝ) * U * L ^ 2 +
          (if i = 0 ∧ j = 0 then K else 0) +
          (if i = m ∧ j = 0 then K else 0)) := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
    _ = 2 * B0 * α * A m + leibnizConstant m * U * L ^ 2 := by
      simp only [Finset.sum_add_distrib]
      simp_rw [ite_and, Finset.sum_ite_irrel]
      simp [leibnizConstant, K, Finset.sum_mul, mul_assoc]
      ring

section Banach

variable {D F E G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The unabridged double Leibniz norm estimate. -/
theorem norm_iteratedFDeriv_trilinear_le
    (B : F →L[ℝ] E →L[ℝ] E →L[ℝ] G) {f : D → F} {a : D → E}
    {m : ℕ} (hf : ContDiff ℝ (m : ℕ∞ω) f) (ha : ContDiff ℝ (m : ℕ∞ω) a) (x : D) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (a y) (a y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (i+1),
        (m.choose i : ℝ) * (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (i-j) a x‖ *
          ‖iteratedFDeriv ℝ (m-i) a x‖ := by
  have houter := norm_iteratedFDeriv_clm_apply ((B.contDiff.comp hf).clm_apply ha) ha x (le_refl _)
  refine houter.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) *
        (‖B‖ * ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (i-j) a x‖) *
          ‖iteratedFDeriv ℝ (m-i) a x‖ := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ m := by simpa using Finset.mem_range.mp hi
      have hinner := B.norm_iteratedFDeriv_le_of_bilinear hf ha x (by exact_mod_cast hi')
      gcongr
      exact hinner
    _ = _ := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A fixed highest-order coefficient, independent of the order `m`. -/
theorem trilinear_jet_bound_top_two
    (B : F →L[ℝ] E →L[ℝ] E →L[ℝ] G) {f : D → F} {a : D → E}
    {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiff ℝ (m : ℕ∞ω) f) (ha : ContDiff ℝ (m : ℕ∞ω) a) (x : D)
    {B0 α U L : ℝ} (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hf0 : ‖f x‖ ≤ B0) (ha0 : ‖a x‖ ≤ α)
    (hfj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ U)
    (haj : ∀ j, j < m → ‖iteratedFDeriv ℝ j a x‖ ≤ L) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (a y) (a y)) x‖ ≤
      2 * ‖B‖ * B0 * α * ‖iteratedFDeriv ℝ m a x‖ +
        ‖B‖ * leibnizConstant m * U * L ^ 2 := by
  apply (norm_iteratedFDeriv_trilinear_le B hf ha x).trans
  have hsum := double_sum_top_two hm
    (fun j => ‖iteratedFDeriv ℝ j f x‖) (fun j => ‖iteratedFDeriv ℝ j a x‖)
    (fun j => norm_nonneg _) (fun j => norm_nonneg _) hU hL
    (by simpa only [norm_iteratedFDeriv_zero] using hf0)
    (by simpa only [norm_iteratedFDeriv_zero] using ha0) hfj haj
  calc
    _ ≤ ‖B‖ * (2 * B0 * α * ‖iteratedFDeriv ℝ m a x‖ +
        leibnizConstant m * U * L ^ 2) := mul_le_mul_of_nonneg_left hsum (norm_nonneg B)
    _ = _ := by ring

/-- A convenient version when a fixed arithmetic constant bounds the trilinear norm. -/
theorem trilinear_jet_bound_top_two_of_norm_le
    (B : F →L[ℝ] E →L[ℝ] E →L[ℝ] G) {f : D → F} {a : D → E}
    {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiff ℝ (m : ℕ∞ω) f) (ha : ContDiff ℝ (m : ℕ∞ω) a) (x : D)
    {c B0 α U L : ℝ} (hc : ‖B‖ ≤ c) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hf0 : ‖f x‖ ≤ B0) (ha0 : ‖a x‖ ≤ α)
    (hfj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ U)
    (haj : ∀ j, j < m → ‖iteratedFDeriv ℝ j a x‖ ≤ L) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (a y) (a y)) x‖ ≤
      2 * c * B0 * α * ‖iteratedFDeriv ℝ m a x‖ +
        c * leibnizConstant m * U * L ^ 2 := by
  have hB0 := (norm_nonneg (f x)).trans hf0
  have hα := (norm_nonneg (a x)).trans ha0
  have hS := leibnizConstant_nonneg m
  apply (trilinear_jet_bound_top_two B hm hf ha x hU hL hf0 ha0 hfj haj).trans
  gcongr

/-- Zeroth order is treated directly and does not use the positive-order endpoint formula. -/
theorem trilinear_jet_bound_zero
    (B : F →L[ℝ] E →L[ℝ] E →L[ℝ] G) (f : D → F) (a : D → E) (x : D)
    {B0 α : ℝ} (hf0 : ‖f x‖ ≤ B0) (ha0 : ‖a x‖ ≤ α) :
    ‖iteratedFDeriv ℝ 0 (fun y => B (f y) (a y) (a y)) x‖ ≤ ‖B‖ * B0 * α ^ 2 := by
  have hB0 := (norm_nonneg (f x)).trans hf0
  have hα := (norm_nonneg (a x)).trans ha0
  rw [norm_iteratedFDeriv_zero]
  calc
    ‖B (f x) (a x) (a x)‖ ≤ ‖B (f x) (a x)‖ * ‖a x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖B (f x)‖ * ‖a x‖) * ‖a x‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((‖B‖ * ‖f x‖) * ‖a x‖) * ‖a x‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((‖B‖ * B0) * α) * α := by gcongr
    _ = _ := by ring

end Banach

end Yau.Proofs.C04Aux.TrilinearJetTopAux
