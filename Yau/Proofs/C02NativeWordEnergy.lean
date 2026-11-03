import Yau.LeafProofs.L21QuantitativeC1
import Yau.Proofs.C02DirectionalJetBounds
import Yau.Proofs.C02DirectionalWordLocality

/-! Finite word-energy evaluation for the one chosen correcting function.
The complete native L21 source receiver supplies the actual energy and Sobolev estimates. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L21Aux
variable {n : ℕ}

theorem native_wordDerivative_eq_directionalWord (v : ComplexVector n → ℂ)
    (w : List (RIdx n)) : wordDerivative v w = directionalWord realVec v w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [wordDerivative, directionalWord, ih]

theorem native_wordDerivative_append (v : ComplexVector n → ℂ) (u w : List (RIdx n)) :
    wordDerivative v (u ++ w) = wordDerivative (wordDerivative v w) u := by
  simp only [native_wordDerivative_eq_directionalWord, directionalWord_append]

theorem native_eventuallyEq_wordDerivative {v v' : ComplexVector n → ℂ} {x : ComplexVector n}
    (h : v =ᶠ[𝓝 x] v') (w : List (RIdx n)) : wordDerivative v w =ᶠ[𝓝 x] wordDerivative v' w := by
  simpa only [native_wordDerivative_eq_directionalWord] using eventuallyEq_directionalWord realVec h w

theorem norm_jet_le_native_word_bound (v : ComplexVector n → ℂ) (hv : ContDiff ℝ ∞ v)
    (m : ℕ) (x : ComplexVector n) (B : ℝ) (hB : 0 ≤ B)
    (hWords : ∀ w : List (RIdx n), w.length = m → ‖wordDerivative v w x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m v x‖ ≤ (realDimension n : ℝ) ^ m * B := by
  apply norm_iteratedFDeriv_le_directional_bound (realBasis n) v hv m x B hB
  intro w hw
  have hBasis : (realBasis n : RIdx n → ComplexVector n) = realVec := funext (realBasis_apply n)
  rw [hBasis, ← native_wordDerivative_eq_directionalWord]
  exact hWords w hw

theorem exists_inner_word_energy_evaluation (m : ℕ) {V R : Set (ComplexVector n)}
    (hV : IsOpen V) (hcV : IsCompact (closure V)) (hR : IsOpen R)
    (hcR : IsCompact (closure R)) (hRV : closure R ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ComplexVector n → ℂ, ContDiff ℝ ∞ v →
      ∀ w : List (RIdx n), w.length ≤ m → ∀ x ∈ R,
      ‖wordDerivative v w x‖ ^ 2 ≤ C * finiteJetEnergy (realDimension n + m) V v := by
  classical
  obtain ⟨χ, hχ, hcχ, hsχ, _hχrange, hχR⟩ :=
    Yau.LeafProofs.L14Aux.exists_model_open_cutoff hV hcR hRV
  let χC : ComplexVector n → ℂ := fun x => (χ x : ℂ)
  have hχC : ContDiff ℝ ∞ χC := Complex.ofRealCLM.contDiff.comp hχ
  have hcχC : HasCompactSupport χC := hcχ.comp_left Complex.ofReal_zero
  have hsχC : tsupport χC ⊆ V := (tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ
  obtain ⟨C1, hC1, hCutoff⟩ := exists_cutoff_word_energy_constant hcV hχC hcχC hsχC (realDimension n + m)
  let P : ℝ := Fintype.card (Finset (Fin (realDimension n)))
  have hP : 0 < P := by dsimp only [P]; exact Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨P * C1, mul_pos hP hC1, ?_⟩
  intro v hv w hw x hx
  have hEq : (fun y => χC y * v y) =ᶠ[𝓝 x] v := by
    filter_upwards [hR.mem_nhds hx] with y hy
    change (χ y : ℂ) * v y = v y
    rw [(hχR y (subset_closure hy)).1, Complex.ofReal_one, one_mul]
  have hWordEq := (native_eventuallyEq_wordDerivative hEq w).eq_of_nhds
  have hSob := complex_compact_pointwise_norm_sq_le
    (contDiff_wordDerivative (hχC.mul hv) w)
    (hasCompactSupport_wordDerivative hcχC.mul_right w) x
  rw [hWordEq] at hSob
  apply hSob.trans
  calc
    _ ≤ ∑ _s : Finset (Fin (realDimension n)), C1 * finiteJetEnergy (realDimension n + m) V v := by
      apply Finset.sum_le_sum
      intro s _
      rw [← native_wordDerivative_append]
      apply hCutoff v hv
      simp only [List.length_append, List.length_map, Finset.length_sort]
      exact Nat.add_le_add (by simpa only [Fintype.card_fin] using s.card_le_univ) hw
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp only [P]; ring

theorem exists_inner_word_column_bound (m : ℕ) {O R : Set (ComplexVector n)}
    (hO : IsOpen O) (hcO : IsCompact (closure O)) (hR : IsOpen R)
    (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ, MatrixSmoothOn A O →
      (∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) →
      JetBound (realDimension n + m) 1 A O →
      ∀ δ : ℝ, 0 ≤ δ → JetBound (realDimension n + m) δ A O →
      ∀ v : ComplexVector n → ℂ, ContDiff ℝ ∞ v → ∀ k : Fin n,
      (∀ x ∈ O, ∀ i, dbarA A i v x = A x i k) →
      ∀ w : List (RIdx n), w.length ≤ m → ∀ x ∈ R,
      ‖wordDerivative v w x‖ ^ 2 ≤ C * ((∫ y in O, ‖v y‖ ^ 2 ∂lebesgueC n) + δ ^ 2) := by
  obtain ⟨V, hV, hRV, hVO, hcV⟩ := exists_open_between_and_isCompact_closure hcR hO hRO
  obtain ⟨C0, hC0, hEnergy⟩ := exists_finiteJetEnergy_bound (realDimension n + m) hO hcO hV hcV hVO
  obtain ⟨C1, hC1, hEval⟩ := exists_inner_word_energy_evaluation m hV hcV hR hcR hRV
  refine ⟨C1 * C0, mul_pos hC1 hC0, ?_⟩
  intro A hA hsmall hJet δ hδ hSmallJet v hv k hEq w hw x hx
  exact (hEval v hv w hw x hx).trans
    ((mul_le_mul_of_nonneg_left (hEnergy A hA hsmall hJet δ hδ hSmallJet v hv k hEq) hC1.le).trans_eq
      (by ring))

end Yau.Blueprint.C02Proof
