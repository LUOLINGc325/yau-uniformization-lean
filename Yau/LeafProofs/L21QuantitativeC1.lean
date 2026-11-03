import Yau.LeafProofs.L21CutoffWordEnergy
import Yau.LeafProofs.L21QuantitativeGradientEvaluation

/-! A fixed inner domain has a uniform pointwise bound for the actual
Fréchet derivative of any smooth solution of a graph-column equation. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem cutoff_fderiv_of_one {χ v : X n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hv : ContDiff ℝ ∞ v) (x : X n) (hc : χ x = 1) (hd : fderiv ℝ χ x = 0) :
    fderiv ℝ (fun y => χ y * v y) x = fderiv ℝ v x := by
  ext z
  rw [fderiv_fun_mul (c := χ) (d := v)
    (hχ.differentiable (by simp) x) (hv.differentiable (by simp) x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hc, hd,
    _root_.zero_apply, mul_zero, add_zero, one_mul]

theorem sobolev_word_length (s : Finset (Fin (realDimension n))) (a : Yau.RIdx n) :
    (((s.sort (· ≤ ·)).map (realIndex n).symm) ++ [a]).length ≤ realDimension n + 1 := by
  simp only [List.length_append, List.length_map, List.length_singleton, Finset.length_sort]
  exact Nat.add_le_add_right (by simpa only [Fintype.card_fin] using s.card_le_univ) 1

theorem exists_inner_fderiv_norm_sq_bound {O R : Set (X n)}
    (hO : IsOpen O) (hcO : IsCompact (closure O)) (hR : IsOpen R)
    (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A O →
      (∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) →
      JetBound (realDimension n + 1) 1 A O →
      ∀ δ : ℝ, 0 ≤ δ → JetBound (realDimension n + 1) δ A O →
      ∀ v : X n → ℂ, ContDiff ℝ ∞ v → ∀ k : Fin n,
      (∀ x ∈ O, ∀ i, dbarA A i v x = A x i k) →
      ∀ x ∈ R, ‖fderiv ℝ v x‖ ^ 2 ≤
        C * ((∫ y in O, ‖v y‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2) := by
  classical
  obtain ⟨V, hV, hRV, hVO, hcV⟩ := exists_open_between_and_isCompact_closure hcR hO hRO
  obtain ⟨χ, hχ, hcχ, hsχ, _hχrange, hχR⟩ :=
    Yau.LeafProofs.L14Aux.exists_model_open_cutoff hV hcR hRV
  let χC : X n → ℂ := fun x => (χ x : ℂ)
  have hχC : ContDiff ℝ ∞ χC := Complex.ofRealCLM.contDiff.comp hχ
  have hcχC : HasCompactSupport χC := hcχ.comp_left Complex.ofReal_zero
  have hsχC : tsupport χC ⊆ V := (tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ
  obtain ⟨C0, hC0, hEnergy⟩ := exists_finiteJetEnergy_bound (realDimension n + 1) hO hcO hV hcV hVO
  obtain ⟨C1, hC1, hCutoff⟩ := exists_cutoff_word_energy_constant hcV hχC hcχC hsχC (realDimension n + 1)
  let P : ℝ := (realDimension n : ℝ) * (Fintype.card (Yau.RIdx n) : ℝ) *
    (Fintype.card (Finset (Fin (realDimension n))) : ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨P * C1 * C0 + 1, by positivity, ?_⟩
  intro A hA hsmall hJet δ hδ hSmallJet v hv k heq x hx
  have hE := hEnergy A hA hsmall hJet δ hδ hSmallJet v hv k heq
  have hDχC : fderiv ℝ χC x = 0 := by
    ext z
    change fderiv ℝ (fun y => (χ y : ℂ)) x z = 0
    rw [fderiv_ofReal_apply (hχ.differentiable (by simp) x), (hχR x (subset_closure hx)).2]
    rfl
  have hχCx : χC x = 1 := by
    change (χ x : ℂ) = 1
    rw [(hχR x (subset_closure hx)).1, Complex.ofReal_one]
  have hSob := complex_compact_fderiv_pointwise_norm_sq_le (hχC.mul hv) hcχC.mul_right x
  rw [cutoff_fderiv_of_one hχC hv x hχCx hDχC] at hSob
  have hSum : (∑ a : Yau.RIdx n, ∑ s : Finset (Fin (realDimension n)),
      ∫ y, ‖wordDerivative (fun z => χC z * v z)
        (((s.sort (· ≤ ·)).map (realIndex n).symm) ++ [a]) y‖ ^ 2 ∂Yau.lebesgueC n) ≤
      (Fintype.card (Yau.RIdx n) : ℝ) *
        ((Fintype.card (Finset (Fin (realDimension n))) : ℝ) *
          (C1 * finiteJetEnergy (realDimension n + 1) V v)) := by
    calc
      _ ≤ ∑ _a : Yau.RIdx n, ∑ _s : Finset (Fin (realDimension n)),
          C1 * finiteJetEnergy (realDimension n + 1) V v := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro s _
        exact hCutoff v hv _ (sobolev_word_length s a)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmass : 0 ≤ (∫ y in O, ‖v y‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2 :=
    add_nonneg (integral_nonneg fun y => sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ (realDimension n : ℝ) *
        (∑ a : Yau.RIdx n, ∑ s : Finset (Fin (realDimension n)),
          ∫ y, ‖wordDerivative (fun z => χC z * v z)
            (((s.sort (· ≤ ·)).map (realIndex n).symm) ++ [a]) y‖ ^ 2 ∂Yau.lebesgueC n) := hSob
    _ ≤ (realDimension n : ℝ) * ((Fintype.card (Yau.RIdx n) : ℝ) *
        ((Fintype.card (Finset (Fin (realDimension n))) : ℝ) *
          (C1 * finiteJetEnergy (realDimension n + 1) V v))) :=
      mul_le_mul_of_nonneg_left hSum (Nat.cast_nonneg _)
    _ = (P * C1) * finiteJetEnergy (realDimension n + 1) V v := by dsimp [P]; ring
    _ ≤ (P * C1) * (C0 * ((∫ y in O, ‖v y‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2)) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hP hC1.le)
    _ = (P * C1 * C0) * ((∫ y in O, ‖v y‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hmass

end Yau.LeafProofs.L21Aux
