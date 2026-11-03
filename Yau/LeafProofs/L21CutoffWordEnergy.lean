import Yau.LeafProofs.L21CutoffWordFormula

/-! Uniform global word energies of a fixed compact cutoff are controlled
by the genuine finite local energy of the original smooth function. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem evalWordTerms_norm_sq_le_products (U : List (Yau.RIdx n) → X n → ℂ)
    (L : List (WordTerm n)) (x : X n) :
    ‖evalWordTerms U L x‖ ^ 2 ≤ (L.length : ℝ) *
      ∑ j : Fin L.length, ‖(L.get j).1 x * U (L.get j).2 x‖ ^ 2 := by
  rw [evalWordTerms_eq_sum_get]
  have hn := norm_sum_le Finset.univ (fun j : Fin L.length => (L.get j).1 x * U (L.get j).2 x)
  have hh := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)).mpr hn
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin L.length => (1 : ℝ))
    (fun j => ‖(L.get j).1 x * U (L.get j).2 x‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hs
  exact hh.trans hs

theorem cutoff_word_energy_bound {R : Set (X n)} (hcR : IsCompact (closure R))
    {χ v : X n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ R) (hv : ContDiff ℝ ∞ v) (q : ℕ) (w : List (Yau.RIdx n))
    (hw : w.length ≤ q) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ γ : List (Yau.RIdx n), γ.length ≤ q → ∀ x, ‖wordDerivative χ γ x‖ ≤ B) :
    (∫ x, ‖wordDerivative (fun y => χ y * v y) w x‖ ^ 2 ∂Yau.lebesgueC n) ≤
      ((2 ^ q : ℕ) : ℝ) ^ 2 * B ^ 2 * finiteJetEnergy q R v := by
  classical
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let L := cutoffWordTerms χ w
  have hs (j : Fin L.length) : tsupport (L.get j).1 ⊆ tsupport χ :=
    cutoffWordTerms_tsupport χ w _ (List.get_mem L j)
  have hcc (j : Fin L.length) : HasCompactSupport (L.get j).1 :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (hs j)
  have hcs (j : Fin L.length) : ContDiff ℝ ∞ (L.get j).1 :=
    cutoffWordTerms_smooth hχ w _ (List.get_mem L j)
  have hi (j : Fin L.length) : Integrable
      (fun x => ‖(L.get j).1 x * wordDerivative v (L.get j).2 x‖ ^ 2) (Yau.lebesgueC n) :=
    (((hcs j).mul (contDiff_wordDerivative hv _)).continuous.memLp_of_hasCompactSupport
      (hcc j).mul_right).integrable_norm_pow (p := 2) (by decide)
  have hbcoeff (j : Fin L.length) (x : X n) : ‖(L.get j).1 x‖ ≤ B := by
    obtain ⟨γ, hlen, he⟩ := cutoffWordTerms_derivative_shape χ w _ (List.get_mem L j)
    rw [he]
    exact hb γ (by omega) x
  have hI (j : Fin L.length) :
      (∫ x, ‖(L.get j).1 x * wordDerivative v (L.get j).2 x‖ ^ 2 ∂Yau.lebesgueC n) ≤
        B ^ 2 * finiteJetEnergy q R v := by
    apply (integral_compact_multiplier_norm_sq_le (L.get j).1 (wordDerivative v (L.get j).2)
      hB (hbcoeff j) ((hs j).trans hsχ) (hi j)
      ((wordDerivative_memLp_restrict hcR hv _).integrable_norm_pow (p := 2) (by decide))).trans
    exact mul_le_mul_of_nonneg_left (wordEnergy_le_finiteJetEnergy q R v _
      ((cutoffWordTerms_order χ w _ (List.get_mem L j)).trans hw)) (sq_nonneg B)
  have hInt : Integrable (fun x => ‖wordDerivative (fun y => χ y * v y) w x‖ ^ 2) (Yau.lebesgueC n) :=
    ((contDiff_wordDerivative (hχ.mul hv) w).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_wordDerivative hcχ.mul_right w)).integrable_norm_pow (p := 2) (by decide)
  have hh := integral_mono hInt
    ((integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul (L.length : ℝ)) (fun x => by
      rw [wordDerivative_cutoff_eq hχ hv w]
      exact evalWordTerms_norm_sq_le_products (wordDerivative v) L x)
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)] at hh
  have hsum : (∑ j : Fin L.length,
      ∫ x, ‖(L.get j).1 x * wordDerivative v (L.get j).2 x‖ ^ 2 ∂Yau.lebesgueC n) ≤
        (L.length : ℝ) * (B ^ 2 * finiteJetEnergy q R v) := by
    calc
      _ ≤ ∑ _j : Fin L.length, B ^ 2 * finiteJetEnergy q R v := Finset.sum_le_sum fun j _ => hI j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlen : (L.length : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
    dsimp only [L]
    rw [length_cutoffWordTerms]
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) hw
  calc
    _ ≤ (L.length : ℝ) * ((L.length : ℝ) * (B ^ 2 * finiteJetEnergy q R v)) :=
      hh.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    _ = (L.length : ℝ) ^ 2 * B ^ 2 * finiteJetEnergy q R v := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hlen)
        (sq_nonneg B)) (finiteJetEnergy_nonneg q R v)

theorem exists_cutoff_word_energy_constant {R : Set (X n)} (hcR : IsCompact (closure R))
    {χ : X n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ R) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : X n → ℂ, ContDiff ℝ ∞ v →
      ∀ w : List (Yau.RIdx n), w.length ≤ q →
      (∫ x, ‖wordDerivative (fun y => χ y * v y) w x‖ ^ 2 ∂Yau.lebesgueC n) ≤
        C * finiteJetEnergy q R v := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_cutoff_word_bound hχ hcχ q
  refine ⟨((2 ^ q : ℕ) : ℝ) ^ 2 * B ^ 2 + 1, by positivity, ?_⟩
  intro v hv w hw
  exact (cutoff_word_energy_bound hcR hχ hcχ hsχ hv q w hw hB.le hb).trans
    (mul_le_mul_of_nonneg_right (by linarith) (finiteJetEnergy_nonneg q R v))

end Yau.LeafProofs.L21Aux
