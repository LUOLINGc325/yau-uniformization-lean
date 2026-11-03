import Yau.Proofs.Y01SequenceEnvelopes
import Yau.Proofs.Y03Grid

/-! Finite closure of coefficient envelopes on the original regular indices. -/
noncomputable section
namespace Yau.Proofs.Y06Aux.GeometricBudget
open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open Yau.Proofs.Y01Aux

/-- A single exponent, independent of the index and of any finite horizon. -/
def Envelope (s : ℕ → ℝ) (reg : ℕ → Prop) (f : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ k, reg k → f k ≤ Real.exp (A * Real.sqrt (s k))

namespace Envelope
variable {s : ℕ → ℝ} {reg : ℕ → Prop} {f g : ℕ → ℝ}

theorem mono (hf : Envelope s reg f) (h : ∀ k, reg k → g k ≤ f k) : Envelope s reg g := by
  obtain ⟨A,hA,hf⟩ := hf
  exact ⟨A,hA,fun k hk => (h k hk).trans (hf k hk)⟩

theorem constant (hs : ∀ k, 1 ≤ s k) (K : ℝ) : Envelope s reg (fun _ => K) := by
  exact ⟨max 0 K, le_max_left _ _, fun k _ =>
    (le_max_right _ _).trans (constant_le_sqrt_envelope (le_max_left _ _) (hs k))⟩

theorem add (hs : ∀ k, 1 ≤ s k) (hf : Envelope s reg f) (hg : Envelope s reg g) :
    Envelope s reg (fun k => f k + g k) := by
  obtain ⟨A,hA,hf⟩ := hf
  obtain ⟨B,hB,hg⟩ := hg
  exact ⟨max A B + Real.log 2, by positivity, fun k hk =>
    exp_sqrt_add_bound (hs k) (hf k hk) (hg k hk)⟩

theorem mul (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : Envelope s reg f) (hg : Envelope s reg g) :
    Envelope s reg (fun k => f k * g k) := by
  obtain ⟨A,hA,hf⟩ := hf
  obtain ⟨B,hB,hg⟩ := hg
  exact ⟨A+B,add_nonneg hA hB,fun k hk =>
    mul_sqrt_envelope (hf0 k) (hg0 k) (hf k hk) (hg k hk)⟩

theorem pow (hf0 : ∀ k, 0 ≤ f k) (hf : Envelope s reg f) (d : ℕ) :
    Envelope s reg (fun k => f k ^ d) := by
  obtain ⟨A,hA,hf⟩ := hf
  exact ⟨d*A,by positivity,fun k hk => pow_sqrt_envelope (hf0 k) (hf k hk) d⟩

theorem polynomial (hs : ∀ k, 1 ≤ s k) (C : ℝ) :
    Envelope s reg (fun k => (1+s k)^C) :=
  ⟨4*|C|,by positivity,fun k _ => polynomial_le_sqrt_envelope (hs k)⟩

end Envelope

/-- Macro-polynomial bounds only require the positive macro-index tail. -/
def MacroBound (j : ℕ → ℕ) (reg : ℕ → Prop) (f : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ k, reg k → 1 ≤ j k → f k ≤ (1+(j k:ℝ))^B

namespace MacroBound
variable {j : ℕ → ℕ} {reg : ℕ → Prop} {f g : ℕ → ℝ}

theorem mono (hf : MacroBound j reg f) (h : ∀ k, reg k → 1 ≤ j k → g k ≤ f k) :
    MacroBound j reg g := by
  obtain ⟨B,hB,hf⟩ := hf
  exact ⟨B,hB,fun k hk hj => (h k hk hj).trans (hf k hk hj)⟩

theorem constant (K : ℝ) : MacroBound j reg (fun _ => K) := by
  obtain ⟨a,ha⟩ := exists_nat_gt K
  refine ⟨a,by positivity,?_⟩
  intro k hk hj
  have hq : (2:ℝ) ≤ 1+(j k:ℝ) := by exact_mod_cast (by omega : 2 ≤ 1+j k)
  have hn : (a:ℝ) ≤ (2:ℝ)^a := by exact_mod_cast (show a < 2^a from Nat.lt_two_pow_self).le
  exact ha.le.trans (hn.trans (by simpa only [Real.rpow_natCast] using
    (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hq a)))

theorem add (hf : MacroBound j reg f) (hg : MacroBound j reg g) :
    MacroBound j reg (fun k => f k+g k) := by
  obtain ⟨A,hA,hf⟩ := hf
  obtain ⟨B,hB,hg⟩ := hg
  refine ⟨max A B+1,by positivity,?_⟩
  intro k hk hj
  have hq : (2:ℝ) ≤ 1+(j k:ℝ) := by exact_mod_cast (by omega : 2 ≤ 1+j k)
  have h₁ := (hf k hk hj).trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left A B))
  have h₂ := (hg k hk hj).trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right A B))
  rw [Real.rpow_add (by positivity), Real.rpow_one]
  nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 1+(j k:ℝ)) (max A B)]

theorem mul (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : MacroBound j reg f) (hg : MacroBound j reg g) :
    MacroBound j reg (fun k => f k*g k) := by
  obtain ⟨A,hA,hf⟩ := hf
  obtain ⟨B,hB,hg⟩ := hg
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro k hk hj
  rw [Real.rpow_add (by positivity)]
  exact mul_le_mul (hf k hk hj) (hg k hk hj) (hg0 k) (Real.rpow_nonneg (by positivity) _)

theorem pow (hf0 : ∀ k, 0 ≤ f k) (hf : MacroBound j reg f) (d : ℕ) :
    MacroBound j reg (fun k => f k^d) := by
  obtain ⟨A,hA,hf⟩ := hf
  refine ⟨A*d,by positivity,?_⟩
  intro k hk hj
  rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
  exact pow_le_pow_left₀ (hf0 k) (hf k hk hj) d

end MacroBound

variable {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}

theorem clock_one_le (hhm : 0 < hm) (k : ℕ) : 1 ≤ gridClock Q N M hm j₀ k := by
  apply le_trans _ (gridClock_mem_Ico Q N M hm hhm j₀ k).1
  exact Real.one_le_exp_iff.mpr (mul_nonneg hhm.le (Nat.cast_nonneg _))

theorem macro_power_envelope (hhm : 0 < hm) {reg : ℕ → Prop} {C : ℝ} (hC : 0 ≤ C) :
    Envelope (gridClock Q N M hm j₀) reg (fun k => (1+(macroAt Q N M hm j₀ k:ℝ))^C) := by
  refine ⟨2*C/hm,by positivity,?_⟩
  intro k hk
  let j := (macroAt Q N M hm j₀ k:ℝ)
  have hroot : Real.exp (hm*j/2) ≤ Real.sqrt (gridClock Q N M hm j₀ k) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (gridClock_mem_Ico Q N M hm hhm j₀ k).1
  have hlin : hm*j/2 ≤ Real.sqrt (gridClock Q N M hm j₀ k) :=
    (show hm*j/2 ≤ Real.exp (hm*j/2) by linarith [Real.add_one_le_exp (hm*j/2)]).trans hroot
  have hlog : Real.log (1+j) ≤ j := by
    have := Real.log_le_sub_one_of_pos (by dsimp [j]; positivity : 0 < 1+j)
    linarith
  change (1+j)^C ≤ _
  rw [Real.rpow_def_of_pos (by dsimp [j]; positivity)]
  apply Real.exp_le_exp.mpr
  have hx : C*j ≤ (2*C/hm)*Real.sqrt (gridClock Q N M hm j₀ k) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hhm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlin hC]
  nlinarith [mul_le_mul_of_nonneg_right hlog hC]

end Yau.Proofs.Y06Aux.GeometricBudget
