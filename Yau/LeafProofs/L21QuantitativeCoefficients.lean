import Yau.LeafProofs.L21QuantitativeWords
import Yau.LeafProofs.L21QuantitativeEnergy

/-! The actual graph rows have uniformly bounded finite jets, and every
word correction coefficient is one negative coordinate derivative of a row. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem norm_iteratedFDeriv_affine_scalar {f : X n → ℂ} {x : X n}
    (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) (c d : ℂ) :
    ‖iteratedFDeriv ℝ k (fun y => c + f y * d) x‖ ≤
      ‖c‖ + ‖d‖ * ‖iteratedFDeriv ℝ k f x‖ := by
  have hk : ContDiffAt ℝ k f x := hf.of_le (by simp)
  have he : (fun y => c + f y * d) = (fun _ : X n => c) + d • f := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hconst : ‖iteratedFDeriv ℝ k (fun _ : X n => c) x‖ ≤ ‖c‖ := by
    cases k with
    | zero => rw [norm_iteratedFDeriv_zero]
    | succ k => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using norm_nonneg c
  rw [he, iteratedFDeriv_add_apply (f := fun _ : X n => c) (g := d • f)
    contDiffAt_const (hk.const_smul d), iteratedFDeriv_const_smul_apply hk]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  exact add_le_add hconst (le_refl _)

theorem norm_iteratedFDeriv_dbarRealCoefficient_le_one {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {q : ℕ} (hJet : JetBound q 1 A O) (k : ℕ) (hk : k ≤ q)
    (x : X n) (hx : x ∈ O) (i : Fin n) (a : Yau.RIdx n) :
    ‖iteratedFDeriv ℝ k (dbarRealCoefficient A i a) x‖ ≤ 1 := by
  have hc : ‖if a.1 = i then wirtBarRealCoefficient a.2 else 0‖ ≤ (1 / 2 : ℝ) := by
    split_ifs
    · exact le_of_eq (norm_wirtBarRealCoefficient _)
    · norm_num
  change ‖iteratedFDeriv ℝ k (fun y => (if a.1 = i then wirtBarRealCoefficient a.2 else 0) +
    A y i a.1 * wirtRealCoefficient a.2) x‖ ≤ 1
  calc
    _ ≤ ‖if a.1 = i then wirtBarRealCoefficient a.2 else 0‖ +
        ‖wirtRealCoefficient a.2‖ * ‖iteratedFDeriv ℝ k (fun y => A y i a.1) x‖ :=
      norm_iteratedFDeriv_affine_scalar ((hA i a.1).contDiffAt (hO.mem_nhds hx)) k _ _
    _ ≤ (1 / 2 : ℝ) + (1 / 2) * 1 := add_le_add hc
      (mul_le_mul (le_of_eq (norm_wirtRealCoefficient _)) (hJet k hk x hx i a.1)
        (norm_nonneg _) (by norm_num))
    _ = 1 := by norm_num

theorem norm_word_dbarRealCoefficient_le_one {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {q : ℕ} (hJet : JetBound q 1 A O) (w : List (Yau.RIdx n)) (hw : w.length ≤ q)
    (x : X n) (hx : x ∈ O) (i : Fin n) (a : Yau.RIdx n) :
    ‖wordDerivative (dbarRealCoefficient A i a) w x‖ ≤ 1 :=
  (norm_wordDerivative_le_iteratedFDeriv w _ x
    ((dbarRealCoefficient_smoothOn hA i a).contDiffAt (hO.mem_nhds hx))).trans
      (norm_iteratedFDeriv_dbarRealCoefficient_le_one hO hA hJet w.length hw x hx i a)

theorem correctionTerms_derivative_shape
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (w : List (Yau.RIdx n)) :
    ∀ t ∈ correctionTerms A i w, ∃ b : Yau.RIdx n, ∃ γ : List (Yau.RIdx n),
      0 < γ.length ∧ 0 < t.2.length ∧ γ.length + t.2.length = w.length + 1 ∧
        t.1 = fun x => -wordDerivative (dbarRealCoefficient A i b) γ x := by
  induction w with
  | nil => simp [correctionTerms]
  | cons a w ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨b, γ, hγ, hsw, hlen, hcoef⟩ := ih s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · refine ⟨b, a :: γ, by simp, hsw, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · funext x
          rw [hcoef]
          simp only [wordDerivative, fderiv_fun_neg, _root_.neg_apply]
      · refine ⟨b, γ, hγ, by simp, ?_, hcoef⟩
        simp only [List.length_cons]
        omega
    · obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp ht
      refine ⟨b, [a], by simp, by simp, ?_, rfl⟩
      simp only [List.length_singleton, List.length_cons, List.length_nil]
      omega

theorem correctionTerms_coefficient_norm_le_one {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {q : ℕ} (hJet : JetBound q 1 A O) (i : Fin n) (w : List (Yau.RIdx n)) (hw : w.length ≤ q)
    (t : WordTerm n) (ht : t ∈ correctionTerms A i w) (x : X n) (hx : x ∈ O) : ‖t.1 x‖ ≤ 1 := by
  obtain ⟨b, γ, _hγ, htw, hlen, hcoef⟩ := correctionTerms_derivative_shape A i w t ht
  have hγq : γ.length ≤ q := by omega
  rw [hcoef, norm_neg]
  exact norm_word_dbarRealCoefficient_le_one hO hA hJet γ hγq x hx i b

theorem length_differentiateWordTerms (a : Yau.RIdx n) (L : List (WordTerm n)) :
    (differentiateWordTerms a L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [differentiateWordTerms, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil]
    change 1 + (1 + 0) + (differentiateWordTerms a L).length = _
    rw [ih]
    ring

theorem length_principalCorrectionTerms (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (a : Yau.RIdx n) (w : List (Yau.RIdx n)) :
    (principalCorrectionTerms A i a w).length = realDimension n := by
  simp only [principalCorrectionTerms, List.length_map, Finset.length_toList, Finset.card_univ, realDimension]

theorem correctionTerms_length_add (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (w : List (Yau.RIdx n)) :
    (correctionTerms A i w).length + realDimension n = realDimension n * 2 ^ w.length := by
  induction w with
  | nil => simp [correctionTerms]
  | cons a w ih =>
    simp only [correctionTerms, List.length_append, length_differentiateWordTerms,
      length_principalCorrectionTerms, List.length_cons, Nat.pow_succ]
    calc
      2 * (correctionTerms A i w).length + realDimension n + realDimension n =
          2 * ((correctionTerms A i w).length + realDimension n) := by ring
      _ = 2 * (realDimension n * 2 ^ w.length) := congrArg (fun z => 2 * z) ih
      _ = _ := by ring

end Yau.LeafProofs.L21Aux
