import Yau.Proofs.Y06GeometricBudgetAlgebra
import Yau.Proofs.Y06JumpNorm
import Yau.Proofs.Y06RateClock

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Yau.Proofs.Y06Aux.GeometricBudget
open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open Yau.Proofs.Y01Aux Yau.Proofs.Y02Aux
open scoped Matrix.Norms.L2Operator

variable {n : ℕ} {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}

 theorem macro_next_power {reg : ℕ → Prop} {C : ℝ} (hC : 0 ≤ C) :
    MacroBound (macroAt Q N M hm j₀) reg
      (fun k => (1+(macroAt Q N M hm j₀ (k+1):ℝ))^C) := by
  refine ⟨2*C,by positivity,?_⟩
  intro k hk hj
  have hnext : macroAt Q N M hm j₀ (k+1) ≤ macroAt Q N M hm j₀ k+1 := by
    rcases macroAt_succ_eq_or Q N M hm j₀ k with h | h <;> omega
  have hnextR : (macroAt Q N M hm j₀ (k+1):ℝ) ≤ (macroAt Q N M hm j₀ k:ℝ)+1 := by exact_mod_cast hnext
  have hjR : (1:ℝ) ≤ (macroAt Q N M hm j₀ k:ℝ) := by exact_mod_cast hj
  have hbase : 1+(macroAt Q N M hm j₀ (k+1):ℝ) ≤ (1+(macroAt Q N M hm j₀ k:ℝ))^2 := by nlinarith
  apply (Real.rpow_le_rpow (by positivity) hbase hC).trans_eq
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

 theorem regular_jump_isUnit
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {L : Changes n} {w : ℕ → Fin n → ℝ} {C c : ℝ}
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) w (macroAt Q N M hm j₀) (macroClock hm) C c L k)
    (k : ℕ) (hk : Regular Q N M (macroAt Q N M hm j₀ k)) :
    IsUnit (if Regular Q N M (macroAt Q N M hm j₀ (k+1)) then alignedJump E L k else 1) := by
  by_cases hn : Regular Q N M (macroAt Q N M hm j₀ (k+1))
  · rw [if_pos hn, alignedJump]
    have hu := jump_unitary hE k
    have hj : IsUnit (jump E k) := ⟨⟨jump E k,(jump E k).conjTranspose,hu.2,hu.1⟩,rfl⟩
    exact ((minus_change_isUnit hE (hL (k+1) hn)).mul hj).mul
      (Matrix.isUnit_nonsing_inv_iff.mpr (plus_change_isUnit (hL k hk)))
  · rw [if_neg hn]
    exact isUnit_one

 theorem regular_jump_macro_bound
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {L : Changes n} {w : ℕ → Fin n → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) w (macroAt Q N M hm j₀) (macroClock hm) C c L k) :
    let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
    let J := fun k => if reg (k+1) then alignedJump E L k else 1
    MacroBound (macroAt Q N M hm j₀) reg (fun k => matOpNorm (J k)+matOpNorm (J k)⁻¹) := by
  dsimp only
  have hbase : MacroBound (macroAt Q N M hm j₀) (fun k => Regular Q N M (macroAt Q N M hm j₀ k))
      (fun k => (1+(macroAt Q N M hm j₀ k:ℝ))^C) := ⟨C,hC,fun _ _ _ => le_rfl⟩
  have hnext := macro_next_power (Q := Q) (N := N) (M := M) (hm := hm) (j₀ := j₀)
    (reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)) hC
  have hsum := hnext.add (MacroBound.constant 2)
  have hp := hsum.pow (fun _ => by positivity) (n+1)
  have hcst := (MacroBound.constant (j := macroAt Q N M hm j₀)
    (reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)) (n+1:ℝ)).mul
    (fun _ => by positivity) (fun _ => by positivity) hp
  have hprod := hbase.mul (fun _ => by positivity) (fun _ => by positivity) hcst
  apply (hprod.add (MacroBound.constant 2)).mono
  intro k hk hj
  apply (regularJump_norm_sum_raw hE hc hL k hk).trans
  split_ifs <;> linarith [show 0 ≤ (1+(macroAt Q N M hm j₀ k:ℝ))^C *
    ((n+1:ℝ)*((1+(macroAt Q N M hm j₀ (k+1):ℝ))^C+2)^(n+1)) by positivity]

 theorem sum_entries_le (A : Herm n) : (∑ i, ∑ l, ‖A i l‖) ≤ (n:ℝ)^2*matOpNorm A := by
  calc
    _ ≤ ∑ _i : Fin n, ∑ _l : Fin n, matOpNorm A :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun l _ => norm_entry_le_matOpNorm A i l))
    _ = _ := by simp [sq,nsmul_eq_mul,mul_assoc]

 theorem uniform_backward_budget
    (hn : 0 < n) {d : ℕ} {scale K eps b : ℝ} (hb : 0 < b)
    (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k+1)) 0‖ =
      Real.exp (-(gridClock Q N M hm j₀ (k+1)-gridClock Q N M hm j₀ k)/2))
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E))
    {L : Changes n} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
        (macroAt Q N M hm j₀) (macroClock hm) C c L k) :
    let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
    let J := fun k => if reg (k+1) then alignedJump E L k else 1
    ∃ CT cT : ℝ, 0 ≤ CT ∧ 0 < cT ∧ ∀ m, 2 ≤ m → m ≤ d → ∀ k, reg k →
      1 ≤ macroAt Q N M hm j₀ k → ∀ X : PolyMap n, Homogeneous X m →
      (backwardOperator (diagonal F tk E k) (J k)
        (weight Q N M hm scale K eps j₀ (rate F tk E) k) X).coeffNorm ≤
        (1+(macroAt Q N M hm j₀ k:ℝ))^CT *
          Real.exp (-cT*Real.sqrt (gridClock Q N M hm j₀ k)/(macroAt Q N M hm j₀ k:ℝ)^2)*X.coeffNorm := by
  dsimp only
  let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
  let J := fun k => if reg (k+1) then alignedJump E L k else 1
  have hnorm := regular_jump_macro_bound hE hC hc hL
  have hlin : MacroBound (macroAt Q N M hm j₀) reg (fun k => (linearPolynomial (J k)).coeffNorm) := by
    apply ((MacroBound.constant ((n:ℝ)^2)).mul (fun _ => by positivity)
      (fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hnorm).mono
    intro k hk hj
    exact (linearPoly_coeffNorm_le_matOpNorm _).trans
      (mul_le_mul_of_nonneg_left (by exact le_add_of_nonneg_right (show 0 ≤ matOpNorm (J k)⁻¹ from norm_nonneg _)) (sq_nonneg _))
  have hentry : MacroBound (macroAt Q N M hm j₀) reg (fun k => ∑ i, ∑ l, ‖(J k)⁻¹ i l‖) := by
    apply ((MacroBound.constant ((n:ℝ)^2)).mul (fun _ => by positivity)
      (fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hnorm).mono
    intro k hk hj
    exact (sum_entries_le _).trans (mul_le_mul_of_nonneg_left
      (by exact le_add_of_nonneg_left (show 0 ≤ matOpNorm (J k) from norm_nonneg _)) (sq_nonneg _))
  have hpow := ((MacroBound.constant 1).add hlin).pow
    (fun k => add_nonneg zero_le_one (coeffNorm_nonneg _)) d
  obtain ⟨CT,hCT,hCTbound⟩ := hentry.mul (fun _ => by positivity)
    (fun k => pow_nonneg (add_nonneg zero_le_one (coeffNorm_nonneg _)) d) hpow
  obtain ⟨cT,hcT,hT⟩ := rate_weight_backward_bound hn hb hgrid hE hdet hweights
  refine ⟨CT,cT,hCT,hcT,?_⟩
  intro m hm2 hmd k hk hj X hX
  have hpowle : (1+(linearPolynomial (J k)).coeffNorm)^m ≤ (1+(linearPolynomial (J k)).coeffNorm)^d :=
    pow_le_pow_right₀ (by linarith [coeffNorm_nonneg (linearPolynomial (J k))]) hmd
  have hfactor := (mul_le_mul_of_nonneg_left hpowle (by positivity : 0 ≤ ∑ i, ∑ l, ‖(J k)⁻¹ i l‖)).trans (hCTbound k hk hj)
  have h := hT k hk (by omega) (J k) m hm2 X hX
  apply h.trans
  have he := mul_le_mul_of_nonneg_left hfactor
    (Real.exp_pos (-cT*Real.sqrt (gridClock Q N M hm j₀ k)/(macroAt Q N M hm j₀ k:ℝ)^2)).le
  have hf := mul_le_mul_of_nonneg_right he (coeffNorm_nonneg X)
  convert hf using 1 <;> ring

end Yau.Proofs.Y06Aux.GeometricBudget
