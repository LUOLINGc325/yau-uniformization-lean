import Yau.LeafProofs.L10InteriorSobolev

/-! The first-letter commutator is bounded in the exact integer-order L² energies. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem ellipticFirstCommutatorJetConstant_nonneg (n k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ ellipticFirstCommutatorJetConstant n k A := by
  unfold ellipticFirstCommutatorJetConstant
  positivity

theorem ellipticFirstCommutatorJetConstant_mono {n j m : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hjm : j ≤ m) :
    ellipticFirstCommutatorJetConstant n j A ≤ ellipticFirstCommutatorJetConstant n m A := by
  unfold ellipticFirstCommutatorJetConstant
  gcongr
  norm_num

def ellipticFirstCommutatorEnergyConstant (n m : ℕ) (A : ℝ) : ℝ :=
  (m + 1 : ℝ) * (ellipticFirstCommutatorJetConstant n m A)^2 * (m + 3)

theorem ellipticFirstCommutator_sobolev_bound {n m : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ p q, ContDiffOn ℝ ∞ (fun y => a y p q) O)
    (hb : ∀ p, ContDiffOn ℝ ∞ (fun y => b y p) O)
    (hu : ContDiffOn ℝ ∞ u O) {A : ℝ} (hA : 0 ≤ A)
    (haBound : ∀ j ≤ m + 1, ∀ x ∈ O, ∀ p q, ‖iteratedFDeriv ℝ j (fun y => a y p q) x‖ ≤ A)
    (hbBound : ∀ j ≤ m + 1, ∀ x ∈ O, ∀ p, ‖iteratedFDeriv ℝ j (fun y => b y p) x‖ ≤ A)
    (hi : ∀ j ≤ m + 2, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j u x‖^2) O (lebesgueC n))
    (i : RIdx n) :
    (∀ j ≤ m, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j (ellipticFirstCommutator a b u i) x‖^2)
      O (lebesgueC n)) ∧
    LeafCandidates.sobolevNormSq O (ellipticFirstCommutator a b u i) m ≤
      ellipticFirstCommutatorEnergyConstant n m A * LeafCandidates.sobolevNormSq O u (m + 2) := by
  classical
  let K := ellipticFirstCommutatorJetConstant n m A
  let D : ℝ := K^2 * (m + 3)
  let U (x : ComplexVector n) := ∑ l ∈ Finset.range (m + 3), ‖iteratedFDeriv ℝ l u x‖^2
  have hK : 0 ≤ K := ellipticFirstCommutatorJetConstant_nonneg _ _ hA
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hU : IntegrableOn U O (lebesgueC n) := integrable_finsetSum _ (fun l hl => hi l (by
    have := Finset.mem_range.mp hl; omega))
  have hPoint (j : ℕ) (hjm : j ≤ m) (x : ComplexVector n) (hx : x ∈ O) :
      ‖iteratedFDeriv ℝ j (ellipticFirstCommutator a b u i) x‖^2 ≤ D * U x := by
    have hjet := ellipticFirstCommutator_jet_bound (k := j) hO ha hb hu hx hA
      (fun l hl p q => haBound l (by omega) x hx p q)
      (fun l hl p => hbBound l (by omega) x hx p) i
    have hsum : (∑ l ∈ Finset.range (j + 3), ‖iteratedFDeriv ℝ l u x‖) ≤
        ∑ l ∈ Finset.range (m + 3), ‖iteratedFDeriv ℝ l u x‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ => norm_nonneg _)
    have hbound : ‖iteratedFDeriv ℝ j (ellipticFirstCommutator a b u i) x‖ ≤
        K * ∑ l ∈ Finset.range (m + 3), ‖iteratedFDeriv ℝ l u x‖ :=
      hjet.trans (mul_le_mul (ellipticFirstCommutatorJetConstant_mono hA hjm) hsum
        (Finset.sum_nonneg fun _ _ => norm_nonneg _) hK)
    have hSq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 3))
      (f := fun l => ‖iteratedFDeriv ℝ l u x‖)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_ofNat] at hCS
    have hmul := mul_le_mul_of_nonneg_left hCS (sq_nonneg K)
    dsimp only [D, U]
    nlinarith
  have hReg := ellipticFirstCommutator_contDiffOn hO ha hb hu i
  have hInts (j : ℕ) (hjm : j ≤ m) : IntegrableOn
      (fun x => ‖iteratedFDeriv ℝ j (ellipticFirstCommutator a b u i) x‖^2) O (lebesgueC n) := by
    have hc : ContinuousOn (fun x => iteratedFDeriv ℝ j (ellipticFirstCommutator a b u i) x) O := by
      intro x hx
      exact ((hReg.contDiffAt (hO.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (m := j) (by exact_mod_cast ENat.natCast_lt_top j)).continuousAt.continuousWithinAt
    apply (hU.const_mul D).mono' ((hc.norm.pow 2).aestronglyMeasurable hO.measurableSet)
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hPoint j hjm x hx
  refine ⟨hInts, ?_⟩
  have hEach (j : ℕ) (hjm : j ≤ m) :
      (∫ x in O, ‖iteratedFDeriv ℝ j (ellipticFirstCommutator a b u i) x‖^2 ∂lebesgueC n) ≤
        D * LeafCandidates.sobolevNormSq O u (m + 2) := by
    have hbound := integral_mono_ae (hInts j hjm) (hU.const_mul D)
      (show ∀ᵐ x ∂(lebesgueC n).restrict O,
        ‖iteratedFDeriv ℝ j (ellipticFirstCommutator a b u i) x‖^2 ≤ D * U x by
        filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
        exact hPoint j hjm x hx)
    rw [integral_const_mul, integral_finsetSum _ (fun l hl => hi l (by
      have := Finset.mem_range.mp hl; omega))] at hbound
    exact hbound
  unfold LeafCandidates.sobolevNormSq
  calc
    _ ≤ ∑ _j ∈ Finset.range (m + 1), D * LeafCandidates.sobolevNormSq O u (m + 2) :=
      Finset.sum_le_sum fun j hj => hEach j (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [ellipticFirstCommutatorEnergyConstant, D, K, LeafCandidates.sobolevNormSq]
      ring

end Yau.LeafProofs
