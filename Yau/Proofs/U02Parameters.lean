import Yau.Blueprint.Nodes

/-! The parameter order in uniformization.tex:11–30 and 78–85.
The jet order is fixed before either model coefficient constant is supplied. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

/-- All decay parameters and the jet order depend only on the original chart
exponents and small-ball contraction constant. -/
theorem choose_decay_parameters {sigma c gamma0 : ℝ}
    (hsigma : 0 < sigma) (hc : 0 < c) (hgamma0 : 0 < gamma0) :
    ∃ (d : ℕ) (sigma' gamma gamma' nu : ℝ),
      2 ≤ d ∧ 0 < sigma' ∧ sigma' ≤ sigma ∧ sigma' ≤ 1 ∧
      0 < gamma ∧ gamma < gamma' ∧ gamma' < sigma' / 2 ∧
      gamma ≤ gamma0 ∧ gamma' < 1 ∧
      0 < nu ∧ nu < 1 / 10 ∧
      10 * nu < c * gamma ∧ 10 * nu < sigma' ∧ 10 * nu < gamma ∧
      30 < ((d : ℝ) + 1) * nu := by
  let sigma' := min sigma 1 / 2
  have hs' : 0 < sigma' := by dsimp [sigma']; positivity
  have hs's : sigma' ≤ sigma := by
    dsimp [sigma']
    linarith [min_le_left sigma (1 : ℝ), lt_min hsigma zero_lt_one]
  have hs'1 : sigma' ≤ 1 := by
    dsimp [sigma']
    linarith [min_le_right sigma (1 : ℝ)]
  let gamma' := min (sigma' / 4) (gamma0 / 2)
  have hg' : 0 < gamma' := by dsimp [gamma']; positivity
  have hg's : gamma' < sigma' / 2 := by
    dsimp [gamma']
    linarith [min_le_left (sigma' / 4) (gamma0 / 2)]
  have hg'g : gamma' ≤ gamma0 / 2 := min_le_right _ _
  let gamma := gamma' / 2
  have hg : 0 < gamma := by dsimp [gamma]; positivity
  have hgg' : gamma < gamma' := by dsimp [gamma]; linarith
  have hgg0 : gamma ≤ gamma0 := by dsimp [gamma]; linarith
  have hg'1 : gamma' < 1 := by linarith
  let a := min (c * gamma) (min sigma' (min gamma 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hac : a ≤ c * gamma := min_le_left _ _
  have has : a ≤ sigma' := (min_le_right _ _).trans (min_le_left _ _)
  have hag : a ≤ gamma :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let nu := a / 20
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have h10 : 10 * nu < a := by dsimp [nu]; linarith
  obtain ⟨D, hD⟩ := exists_nat_gt (30 / nu)
  let d := max 2 D
  have hDd : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_max_right 2 D
  have hdnu : 30 < ((d : ℝ) + 1) * nu := by
    have hDnu : 30 < (D : ℝ) * nu := (div_lt_iff₀ hnu).mp hD
    nlinarith
  exact ⟨d, sigma', gamma, gamma', nu, le_max_left _ _, hs', hs's, hs'1,
    hg, hgg', hg's, hgg0, hg'1, hnu, by dsimp [nu]; linarith,
    h10.trans_le hac, h10.trans_le has, h10.trans_le hag, hdnu⟩

/-- Only after the decay/jet parameters, arbitrary fixed-degree coefficient
constants determine the macro width. -/
theorem choose_macro_width {nu : ℝ} (hnu : 0 < nu) (A C : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ h0 ≤ 1 ∧
      ∀ hm : ℝ, 0 < hm → hm < h0 →
        Real.exp hm - 1 < 1 / 10 ∧
        A * (Real.exp hm - 1) < 1 ∧
        C * (Real.exp hm - 1) < nu / 4 := by
  let B := max 1 (max |A| |C|)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hAB : A ≤ B := (le_abs_self A).trans
    ((le_max_left |A| |C|).trans (le_max_right _ _))
  have hCB : C ≤ B := (le_abs_self C).trans
    ((le_max_right |A| |C|).trans (le_max_right _ _))
  let eps := min (1 / (20 * B)) (nu / (8 * B))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsA : eps ≤ 1 / (20 * B) := min_le_left _ _
  have hepsC : eps ≤ nu / (8 * B) := min_le_right _ _
  have hlog : 0 < Real.log (1 + eps) := Real.log_pos (by linarith)
  refine ⟨min 1 (Real.log (1 + eps)), lt_min zero_lt_one hlog,
    min_le_left _ _, ?_⟩
  intro hm hhm hmh0
  have hmLog : hm < Real.log (1 + eps) :=
    hmh0.trans_le (min_le_right _ _)
  have hd : 0 < Real.exp hm - 1 := by
    have := Real.one_lt_exp_iff.mpr hhm
    linarith
  have hde : Real.exp hm - 1 < eps := by
    have hexp := Real.exp_lt_exp.mpr hmLog
    rw [Real.exp_log (by linarith : 0 < 1 + eps)] at hexp
    linarith
  have hBeA : B * eps ≤ 1 / 20 := by
    have := mul_le_mul_of_nonneg_left hepsA hB.le
    field_simp at this ⊢
    nlinarith
  have hBeC : B * eps ≤ nu / 8 := by
    have := mul_le_mul_of_nonneg_left hepsC hB.le
    field_simp at this ⊢
    nlinarith
  have hBd : B * (Real.exp hm - 1) < B * eps :=
    mul_lt_mul_of_pos_left hde hB
  have hA := mul_le_mul_of_nonneg_right hAB hd.le
  have hC := mul_le_mul_of_nonneg_right hCB hd.le
  refine ⟨?_, by linarith, by linarith⟩
  have hsmall : eps ≤ 1 / 20 := by
    have : (1 : ℝ) / (20 * B) ≤ 1 / 20 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 20 * B) (by norm_num)).2
      nlinarith
    exact hepsA.trans this
  linarith

end Yau.NodeProofs.U02Proof
