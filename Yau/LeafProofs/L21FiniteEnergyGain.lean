import Yau.LeafProofs.L21GraphWordEnergy

/-! One quantitative gain controls every coordinate word of the next order
on an inner domain. All constants precede the coefficients and solution. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem exists_word_energy_gain_constant (q : ℕ) {O R : Set (X n)}
    (hO : IsOpen O) (hcO : IsCompact (closure O)) (hR : IsOpen R)
    (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A O →
      (∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) → JetBound q 1 A O →
      ∀ δ : ℝ, 0 ≤ δ → JetBound q δ A O →
      ∀ (v : X n → ℂ), ContDiff ℝ ∞ v → ∀ k : Fin n,
      (∀ x ∈ O, ∀ i, dbarA A i v x = A x i k) →
      ∀ w : List (Yau.RIdx n), w.length ≤ q + 1 →
        wordEnergy R v w ≤ C * (finiteJetEnergy q O v + δ ^ 2) := by
  classical
  obtain ⟨C0, hC0, hBase⟩ := exists_inner_gradient_energy_bound hO hR hcR hRO
  let volO : ℝ := ∫ x in O, (1 : ℝ) ∂Yau.lebesgueC n
  let M : ℝ := (realDimension n : ℝ) * 2 ^ q
  let aC : ℝ := 1 + 2 * (n : ℝ) * M ^ 2
  let bC : ℝ := 2 * (n : ℝ) * volO
  let D : ℝ := aC + bC
  let C : ℝ := 1 + C0 * D
  have hvO : 0 ≤ volO := integral_nonneg fun _ => by norm_num
  have haC : 0 ≤ aC := by dsimp [aC]; positivity
  have hbC : 0 ≤ bC := by dsimp [bC]; positivity
  have hD : 0 ≤ D := add_nonneg haC hbC
  have hC1 : 1 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hC0.le hD]
  refine ⟨C, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hC1, ?_⟩
  intro A hA hsmall hJet δ hδ hSmallJet v hv k heq w hw
  let E := finiteJetEnergy q O v
  have hE : 0 ≤ E := finiteJetEnergy_nonneg q O v
  have hEδ : 0 ≤ E + δ ^ 2 := add_nonneg hE (sq_nonneg δ)
  have hJet0 : JetBound 0 1 A O := by
    intro m hm x hx i j
    exact hJet m (hm.trans (Nat.zero_le q)) x hx i j
  cases w with
  | nil =>
    have hword : wordEnergy R v [] ≤ E :=
      (wordEnergy_mono (subset_closure.trans hRO) v []
        ((wordDerivative_memLp_restrict hcO hv []).integrable_norm_pow (p := 2) (by decide))).trans
        (wordEnergy_le_finiteJetEnergy q O v [] (Nat.zero_le q))
    apply hword.trans
    calc
      E ≤ E + δ ^ 2 := le_add_of_nonneg_right (sq_nonneg δ)
      _ ≤ C * (E + δ ^ 2) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 hEδ
  | cons a w =>
    have hwq : w.length ≤ q := by simp only [List.length_cons] at hw; omega
    have hGraph (i : Fin n) := graph_word_energy_bound hO hcO hA hδ hJet hSmallJet v hv k heq w hwq i
    have hLocal := hBase A hA hsmall hJet0 (wordDerivative v w) (contDiff_wordDerivative hv w)
      (wordDerivative_memLp_restrict hcO hv w) (fun i => (hGraph i).1)
    have hSingle : wordEnergy R v (a :: w) ≤
        ∑ b : Yau.RIdx n, ∫ x in R, ‖fderiv ℝ (wordDerivative v w) x (Yau.realVec b)‖ ^ 2 ∂Yau.lebesgueC n := by
      exact Finset.single_le_sum (f := fun b : Yau.RIdx n =>
        ∫ x in R, ‖fderiv ℝ (wordDerivative v w) x (Yau.realVec b)‖ ^ 2 ∂Yau.lebesgueC n)
        (fun b _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ a)
    have hSum : (∑ i : Fin n, ∫ x in O, ‖dbarA A i (wordDerivative v w) x‖ ^ 2 ∂Yau.lebesgueC n) ≤
        (n : ℝ) * (2 * δ ^ 2 * volO + 2 * M ^ 2 * E) := by
      calc
        _ ≤ ∑ _i : Fin n, (2 * δ ^ 2 * volO + 2 * M ^ 2 * E) :=
          Finset.sum_le_sum fun i _ => (hGraph i).2
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply (hSingle.trans hLocal).trans
    apply (mul_le_mul_of_nonneg_left
      (add_le_add (wordEnergy_le_finiteJetEnergy q O v w hwq) hSum) hC0.le).trans
    change C0 * (E + (n : ℝ) * (2 * δ ^ 2 * volO + 2 * M ^ 2 * E)) ≤ C * (E + δ ^ 2)
    have hAlg : E + (n : ℝ) * (2 * δ ^ 2 * volO + 2 * M ^ 2 * E) = aC * E + bC * δ ^ 2 := by
      dsimp [aC, bC]
      ring
    rw [hAlg]
    have haD : aC ≤ D := by dsimp [D]; linarith
    have hbD : bC ≤ D := by dsimp [D]; linarith
    have hBound : aC * E + bC * δ ^ 2 ≤ D * (E + δ ^ 2) := by
      calc
        _ ≤ D * E + D * δ ^ 2 := add_le_add (mul_le_mul_of_nonneg_right haD hE)
          (mul_le_mul_of_nonneg_right hbD (sq_nonneg δ))
        _ = _ := by ring
    apply (mul_le_mul_of_nonneg_left hBound hC0.le).trans
    have hh := mul_le_mul_of_nonneg_right (show C0 * D ≤ C by dsimp [C]; linarith) hEδ
    simpa only [mul_assoc] using hh

theorem exists_finiteJetEnergy_gain_constant (q : ℕ) {O R : Set (X n)}
    (hO : IsOpen O) (hcO : IsCompact (closure O)) (hR : IsOpen R)
    (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A O →
      (∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) → JetBound q 1 A O →
      ∀ δ : ℝ, 0 ≤ δ → JetBound q δ A O →
      ∀ (v : X n → ℂ), ContDiff ℝ ∞ v → ∀ k : Fin n,
      (∀ x ∈ O, ∀ i, dbarA A i v x = A x i k) →
        finiteJetEnergy (q + 1) R v ≤ C * (finiteJetEnergy q O v + δ ^ 2) := by
  classical
  obtain ⟨C0, hC0, hWords⟩ := exists_word_energy_gain_constant q hO hcO hR hcR hRO
  let N : ℝ := ∑ m ∈ Finset.range (q + 2), (Fintype.card (Fin m → Yau.RIdx n) : ℝ)
  have hN : 0 ≤ N := Finset.sum_nonneg fun m _ => Nat.cast_nonneg _
  refine ⟨(N + 1) * C0, by positivity, ?_⟩
  intro A hA hsmall hJet δ hδ hSmallJet v hv k heq
  have hNonneg : 0 ≤ C0 * (finiteJetEnergy q O v + δ ^ 2) :=
    mul_nonneg hC0.le (add_nonneg (finiteJetEnergy_nonneg q O v) (sq_nonneg δ))
  calc
    _ ≤ ∑ m ∈ Finset.range (q + 2), ∑ _a : Fin m → Yau.RIdx n,
        C0 * (finiteJetEnergy q O v + δ ^ 2) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro a _
      exact hWords A hA hsmall hJet δ hδ hSmallJet v hv k heq (List.ofFn a)
        (by simp only [List.length_ofFn]; exact Nat.le_of_lt_succ (Finset.mem_range.mp hm))
    _ = N * (C0 * (finiteJetEnergy q O v + δ ^ 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.sum_mul]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (by linarith : N ≤ N + 1) hNonneg
      simpa only [mul_assoc] using hh

end Yau.LeafProofs.L21Aux
