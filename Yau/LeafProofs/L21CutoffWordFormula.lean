import Yau.LeafProofs.L21FiniteEnergyInduction

/-! The finite cutoff expressions are the actual derivatives of a smooth
product. Their coefficient bounds depend only on the fixed cutoff and order. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem contDiff_evalWordTerms (U : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n))
    (hc : ∀ t ∈ L, ContDiff ℝ ∞ t.1) (hU : ∀ w, ContDiff ℝ ∞ (U w)) :
    ContDiff ℝ ∞ (evalWordTerms U L) := by
  simpa only [contDiffOn_univ] using contDiffOn_evalWordTerms (O := Set.univ) U L
    (fun t ht => (hc t ht).contDiffOn) (fun t _ => (hU t.2).contDiffOn)

theorem fderiv_evalWordTerms (U : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n))
    (hc : ∀ t ∈ L, ContDiff ℝ ∞ t.1) (hU : ∀ w, ContDiff ℝ ∞ (U w))
    (hDU : ∀ w a x, fderiv ℝ (U w) x (Yau.realVec a) = U (a :: w) x)
    (a : Yau.RIdx n) (x : X n) :
    fderiv ℝ (evalWordTerms U L) x (Yau.realVec a) = evalWordTerms U (differentiateWordTerms a L) x := by
  induction L with
  | nil =>
    change fderiv ℝ (fun _ : X n => (0 : ℂ)) x (Yau.realVec a) = 0
    rw [fderiv_fun_const]
    rfl
  | cons t L ih =>
    have hct := hc t (List.mem_cons_self)
    have hcL := fun s hs => hc s (List.mem_cons_of_mem t hs)
    have hdhead := (hct.differentiable (by simp) x).mul ((hU t.2).differentiable (by simp) x)
    have hdtail := (contDiff_evalWordTerms U L hcL hU).differentiable (by simp) x
    change fderiv ℝ (fun y => t.1 y * U t.2 y + evalWordTerms U L y) x (Yau.realVec a) = _
    rw [fderiv_fun_add (f := fun y => t.1 y * U t.2 y) (g := evalWordTerms U L) hdhead hdtail,
      _root_.add_apply, fderiv_fun_mul (c := t.1) (d := U t.2)
        (hct.differentiable (by simp) x) ((hU t.2).differentiable (by simp) x)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hDU, ih hcL,
      eval_differentiateWordTerms_cons]
    ring

theorem wordDerivative_cutoff_eq {χ v : X n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hv : ContDiff ℝ ∞ v)
    (w : List (Yau.RIdx n)) :
    wordDerivative (fun x => χ x * v x) w = cutoffWordJet χ (wordDerivative v) w := by
  induction w with
  | nil =>
    funext x
    change χ x * v x = χ x * v x + 0
    ring
  | cons a w ih =>
    change (fun x => fderiv ℝ (wordDerivative (fun y => χ y * v y) w) x (Yau.realVec a)) = _
    rw [ih]
    funext x
    exact fderiv_evalWordTerms (wordDerivative v) (cutoffWordTerms χ w)
      (cutoffWordTerms_smooth hχ w) (fun u => contDiff_wordDerivative hv u) (fun _ _ _ => rfl) a x

theorem cutoffWordTerms_derivative_shape (χ : X n → ℂ) (w : List (Yau.RIdx n)) :
    ∀ t ∈ cutoffWordTerms χ w, ∃ γ : List (Yau.RIdx n),
      γ.length + t.2.length = w.length ∧ t.1 = wordDerivative χ γ := by
  induction w with
  | nil =>
    intro t ht
    have he : t = (χ, []) := List.mem_singleton.mp ht
    subst t
    exact ⟨[], rfl, rfl⟩
  | cons a w ih =>
    intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨γ, hlen, hcoef⟩ := ih s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨a :: γ, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · rw [hcoef]
        rfl
    · refine ⟨γ, ?_, hcoef⟩
      simp only [List.length_cons]
      omega

theorem length_cutoffWordTerms (χ : X n → ℂ) (w : List (Yau.RIdx n)) :
    (cutoffWordTerms χ w).length = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [cutoffWordTerms, length_differentiateWordTerms, ih, List.length_cons, Nat.pow_succ]
    ring

theorem exists_uniform_cutoff_word_bound {χ : X n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (q : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ w : List (Yau.RIdx n), w.length ≤ q → ∀ x, ‖wordDerivative χ w x‖ ≤ B := by
  classical
  have hex (m : ℕ) (a : Fin m → Yau.RIdx n) : ∃ C : ℝ, ∀ x, ‖wordDerivative χ (List.ofFn a) x‖ ≤ C :=
    (hasCompactSupport_wordDerivative hcχ _).exists_bound_of_continuous (contDiff_wordDerivative hχ _).continuous
  choose C hC using hex
  let S : ℝ := ∑ m ∈ Finset.range (q + 1), ∑ a : Fin m → Yau.RIdx n, max (C m a) 0
  have hS : 0 ≤ S := Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun a _ => le_max_right _ _
  refine ⟨S + 1, by positivity, ?_⟩
  intro w hw x
  have hbase : ‖wordDerivative χ w x‖ ≤ C w.length w.get := by
    simpa only [List.ofFn_get] using hC w.length w.get x
  have hsingle : max (C w.length w.get) 0 ≤ ∑ a : Fin w.length → Yau.RIdx n, max (C w.length a) 0 :=
    Finset.single_le_sum (f := fun a : Fin w.length → Yau.RIdx n => max (C w.length a) 0)
      (fun a _ => le_max_right _ _) (Finset.mem_univ w.get)
  have houter : (∑ a : Fin w.length → Yau.RIdx n, max (C w.length a) 0) ≤ S :=
    Finset.single_le_sum (f := fun m : ℕ => ∑ a : Fin m → Yau.RIdx n, max (C m a) 0)
      (fun m _ => Finset.sum_nonneg fun a _ => le_max_right _ _)
      (Finset.mem_range.mpr (by omega))
  exact hbase.trans ((le_max_left _ _).trans (hsingle.trans (houter.trans (by linarith))))

end Yau.LeafProofs.L21Aux
