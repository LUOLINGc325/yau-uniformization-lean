import Yau.LeafProofs.L21FiniteEnergyGain

/-! The finite-order energy estimate closes on nested inner domains with
constants chosen uniformly before the smooth graph and its column solution. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem jetBound_mono_order {A : X n → Matrix (Fin n) (Fin n) ℂ} {O : Set (X n)}
    {r q : ℕ} {b : ℝ} (hrq : r ≤ q) (hJet : JetBound q b A O) : JetBound r b A O :=
  fun k hk x hx i j => hJet k (hk.trans hrq) x hx i j

theorem jetBound_mono_domain {A : X n → Matrix (Fin n) (Fin n) ℂ} {O V : Set (X n)}
    {q : ℕ} {b : ℝ} (hVO : V ⊆ O) (hJet : JetBound q b A O) : JetBound q b A V :=
  fun k hk x hx i j => hJet k hk x (hVO hx) i j

theorem exists_finiteJetEnergy_bound (q : ℕ) {O R : Set (X n)}
    (hO : IsOpen O) (hcO : IsCompact (closure O)) (hR : IsOpen R)
    (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A O →
      (∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) → JetBound q 1 A O →
      ∀ δ : ℝ, 0 ≤ δ → JetBound q δ A O →
      ∀ (v : X n → ℂ), ContDiff ℝ ∞ v → ∀ k : Fin n,
      (∀ x ∈ O, ∀ i, dbarA A i v x = A x i k) →
        finiteJetEnergy q R v ≤ C * ((∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2) := by
  induction q generalizing R with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro A hA hsmall hJet δ hδ hSmallJet v hv k heq
    rw [finiteJetEnergy_zero, one_mul]
    have hh := wordEnergy_mono (subset_closure.trans hRO) v []
      ((wordDerivative_memLp_restrict hcO hv []).integrable_norm_pow (p := 2) (by decide))
    change (∫ x in R, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) ≤ ∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n at hh
    exact hh.trans (le_add_of_nonneg_right (sq_nonneg δ))
  | succ q ih =>
    obtain ⟨W, hW, hRW, hWO, hcW⟩ := exists_open_between_and_isCompact_closure hcR hO hRO
    obtain ⟨C0, hC0, hOld⟩ := ih (R := W) hW hcW hWO
    obtain ⟨C1, hC1, hGain⟩ := exists_finiteJetEnergy_gain_constant q hW hcW hR hcR hRW
    refine ⟨C1 * (C0 + 1), by positivity, ?_⟩
    intro A hA hsmall hJet δ hδ hSmallJet v hv k heq
    have hWO0 : W ⊆ O := subset_closure.trans hWO
    have hJetq := jetBound_mono_order (Nat.le_succ q) hJet
    have hSmallJetq := jetBound_mono_order (Nat.le_succ q) hSmallJet
    have hBefore := hOld A hA hsmall hJetq δ hδ hSmallJetq v hv k heq
    have hAfter := hGain A (fun i j => (hA i j).mono hWO0)
      (fun x hx => hsmall x (hWO0 hx)) (jetBound_mono_domain hWO0 hJetq)
      δ hδ (jetBound_mono_domain hWO0 hSmallJetq) v hv k (fun x hx => heq x (hWO0 hx))
    have hU : 0 ≤ ∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n := integral_nonneg fun x => sq_nonneg _
    have hδbound : δ ^ 2 ≤ (∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2 := by linarith
    calc
      _ ≤ C1 * (finiteJetEnergy q W v + δ ^ 2) := hAfter
      _ ≤ C1 * (C0 * ((∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2) + δ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hBefore (le_refl _)) hC1.le
      _ ≤ C1 * (C0 * ((∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2) +
          ((∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hδbound) hC1.le
      _ = _ := by ring

end Yau.LeafProofs.L21Aux
