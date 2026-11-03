import Yau.LeafProofs.L10InteriorSuccessorNorm

/-! Higher jets of the first-letter commutator contain only lower jets of `u`. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem elliptic_sum_jet_norm_le {n k : ℕ} {ι : Type*} {S : Finset ι}
    {f : ι → ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hf : ∀ j ∈ S, ContDiffOn ℝ ∞ (f j) O) {x : ComplexVector n} (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ j ∈ S, f j y) x‖ ≤
      ∑ j ∈ S, ‖iteratedFDeriv ℝ k (f j) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun j hj =>
    ((hf j hj).contDiffAt (hO.mem_nhds hx)).of_le (by simp))]
  exact norm_sum_le _ _

def ellipticFirstCommutatorJetConstant (n k : ℕ) (A : ℝ) : ℝ :=
  ((Fintype.card (RIdx n) : ℝ)^2 + Fintype.card (RIdx n)) * A * 2^k * (k + 1)

theorem ellipticFirstCommutator_jet_bound {n k : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ p q, ContDiffOn ℝ ∞ (fun y => a y p q) O)
    (hb : ∀ p, ContDiffOn ℝ ∞ (fun y => b y p) O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O)
    {A : ℝ} (hA : 0 ≤ A)
    (haBound : ∀ j ≤ k + 1, ∀ p q, ‖iteratedFDeriv ℝ j (fun y => a y p q) x‖ ≤ A)
    (hbBound : ∀ j ≤ k + 1, ∀ p, ‖iteratedFDeriv ℝ j (fun y => b y p) x‖ ≤ A)
    (i : RIdx n) :
    ‖iteratedFDeriv ℝ k (ellipticFirstCommutator a b u i) x‖ ≤
      ellipticFirstCommutatorJetConstant n k A *
        ∑ j ∈ Finset.range (k + 3), ‖iteratedFDeriv ℝ j u x‖ := by
  classical
  let S : ℝ := ∑ j ∈ Finset.range (k + 3), ‖iteratedFDeriv ℝ j u x‖
  let Q : ℝ := A * 2^k * (k + 1) * S
  let Af (p q : RIdx n) (y : ComplexVector n) :=
    ellipticPartial (fun z => a z p q) i y • ellipticPartial (ellipticPartial u q) p y
  let Bf (p : RIdx n) (y : ComplexVector n) :=
    ellipticPartial (fun z => b z p) i y • ellipticPartial u p y
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have huBound (j : ℕ) (hj : j ≤ k + 2) : ‖iteratedFDeriv ℝ j u x‖ ≤ S :=
    Finset.single_le_sum (s := Finset.range (k + 3))
      (f := fun l => ‖iteratedFDeriv ℝ l u x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hAsmooth (p q : RIdx n) : ContDiffOn ℝ ∞ (Af p q) O :=
    (ellipticPartial_contDiffOn hO (ha p q) i).smul
      (ellipticPartial_contDiffOn hO (ellipticPartial_contDiffOn hO hu q) p)
  have hBsmooth (p : RIdx n) : ContDiffOn ℝ ∞ (Bf p) O :=
    (ellipticPartial_contDiffOn hO (hb p) i).smul (ellipticPartial_contDiffOn hO hu p)
  have hAbound (p q : RIdx n) : ‖iteratedFDeriv ℝ k (Af p q) x‖ ≤ Q := by
    have hprod := elliptic_product_jet_bound (k := k) hO (ellipticPartial_contDiffOn hO (ha p q) i)
      (ellipticPartial_contDiffOn hO (ellipticPartial_contDiffOn hO hu q) p) hx hA
      (fun j hj => (elliptic_directional_jet_norm_le hO (ha p q) hx i j).trans
        (haBound (j + 1) (by omega) p q))
    apply hprod.trans
    calc
      _ ≤ (A * 2^k) * ∑ _j ∈ Finset.range (k + 1), S := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
        exact ((elliptic_directional_jet_norm_le hO (ellipticPartial_contDiffOn hO hu q) hx p j).trans
          (elliptic_directional_jet_norm_le hO hu hx q (j + 1))).trans
          (huBound (j + 1 + 1) (by omega))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp only [Q]
        push_cast
        ring
  have hBbound (p : RIdx n) : ‖iteratedFDeriv ℝ k (Bf p) x‖ ≤ Q := by
    have hprod := elliptic_product_jet_bound (k := k) hO (ellipticPartial_contDiffOn hO (hb p) i)
      (ellipticPartial_contDiffOn hO hu p) hx hA
      (fun j hj => (elliptic_directional_jet_norm_le hO (hb p) hx i j).trans
        (hbBound (j + 1) (by omega) p))
    apply hprod.trans
    calc
      _ ≤ (A * 2^k) * ∑ _j ∈ Finset.range (k + 1), S := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
        exact (elliptic_directional_jet_norm_le hO hu hx p j).trans (huBound (j + 1) (by omega))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp only [Q]
        push_cast
        ring
  have hSumA : ‖iteratedFDeriv ℝ k (fun y => ∑ p, ∑ q, Af p q y) x‖ ≤
      (Fintype.card (RIdx n) : ℝ)^2 * Q := by
    apply (elliptic_sum_jet_norm_le hO (fun p _ => ContDiffOn.sum (fun q _ => hAsmooth p q)) hx).trans
    calc
      _ ≤ ∑ p : RIdx n, ∑ _q : RIdx n, Q := by
        apply Finset.sum_le_sum
        intro p _
        exact (elliptic_sum_jet_norm_le hO (fun q _ => hAsmooth p q) hx).trans
          (Finset.sum_le_sum fun q _ => hAbound p q)
      _ = _ := by simp; ring
  have hSumB : ‖iteratedFDeriv ℝ k (fun y => ∑ p, Bf p y) x‖ ≤
      (Fintype.card (RIdx n) : ℝ) * Q :=
    (elliptic_sum_jet_norm_le hO (fun p _ => hBsmooth p) hx).trans
      (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun p _ => hBbound p))
  change ‖iteratedFDeriv ℝ k (fun y => (∑ p, ∑ q, Af p q y) + ∑ p, Bf p y) x‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply
    (((ContDiffOn.sum fun p _ => ContDiffOn.sum fun q _ => hAsmooth p q).contDiffAt
      (hO.mem_nhds hx)).of_le (by simp))
    (((ContDiffOn.sum fun p _ => hBsmooth p).contDiffAt (hO.mem_nhds hx)).of_le (by simp))]
  apply (norm_add_le _ _).trans
  apply (add_le_add hSumA hSumB).trans_eq
  dsimp only [ellipticFirstCommutatorJetConstant, Q, S]
  ring

end Yau.LeafProofs
