import Yau.LeafProofs.L21QuantitativeLocalEnergy
import Yau.LeafProofs.L21QuantitativeEvaluation

/-! Finite sums of actual coordinate-word squared energies. Every word
through the designated order has one literal summand. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def wordEnergy (O : Set (X n)) (v : X n → ℂ) (w : List (Yau.RIdx n)) : ℝ :=
  ∫ x in O, ‖wordDerivative v w x‖ ^ 2 ∂Yau.lebesgueC n

def finiteJetEnergy (q : ℕ) (O : Set (X n)) (v : X n → ℂ) : ℝ :=
  ∑ m ∈ Finset.range (q + 1), ∑ a : Fin m → Yau.RIdx n, wordEnergy O v (List.ofFn a)

theorem wordEnergy_nonneg (O : Set (X n)) (v : X n → ℂ) (w : List (Yau.RIdx n)) :
    0 ≤ wordEnergy O v w := integral_nonneg fun x => sq_nonneg _

theorem finiteJetEnergy_nonneg (q : ℕ) (O : Set (X n)) (v : X n → ℂ) :
    0 ≤ finiteJetEnergy q O v :=
  Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun a _ => wordEnergy_nonneg O v _

theorem wordEnergy_le_finiteJetEnergy (q : ℕ) (O : Set (X n)) (v : X n → ℂ)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) : wordEnergy O v w ≤ finiteJetEnergy q O v := by
  classical
  have hm : w.length ∈ Finset.range (q + 1) := Finset.mem_range.mpr (by omega)
  have hsingle : wordEnergy O v w ≤ ∑ a : Fin w.length → Yau.RIdx n, wordEnergy O v (List.ofFn a) := by
    have hh := Finset.single_le_sum (f := fun a : Fin w.length → Yau.RIdx n => wordEnergy O v (List.ofFn a))
      (fun a _ => wordEnergy_nonneg O v _) (Finset.mem_univ w.get)
    simpa only [List.ofFn_get] using hh
  exact hsingle.trans (Finset.single_le_sum
    (f := fun m : ℕ => ∑ a : Fin m → Yau.RIdx n, wordEnergy O v (List.ofFn a))
    (fun m _ => Finset.sum_nonneg fun a _ => wordEnergy_nonneg O v _) hm)

theorem finiteJetEnergy_zero (O : Set (X n)) (v : X n → ℂ) :
    finiteJetEnergy 0 O v = ∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n := by
  simp only [finiteJetEnergy, Nat.zero_add, Finset.range_one, Finset.sum_singleton]
  have he : ∀ a : Fin 0 → Yau.RIdx n, List.ofFn a = [] := fun a => List.length_eq_zero_iff.mp (by simp)
  simp only [he, Fintype.sum_unique, wordEnergy, wordDerivative]

theorem wordDerivative_memLp_restrict {O : Set (X n)} (hcO : IsCompact (closure O))
    {v : X n → ℂ} (hv : ContDiff ℝ ∞ v) (w : List (Yau.RIdx n)) :
    MemLp (wordDerivative v w) 2 ((Yau.lebesgueC n).restrict O) := by
  have hm : MemLp (wordDerivative v w) 2 ((Yau.lebesgueC n).restrict (closure O)) :=
    locallyL2On_of_continuousOn (O := Set.univ) (contDiff_wordDerivative hv w).continuous.continuousOn
      (closure O) hcO (Set.subset_univ _)
  exact hm.mono_measure (Measure.restrict_mono subset_closure le_rfl)

theorem wordEnergy_mono {O V : Set (X n)} (hVO : V ⊆ O) (v : X n → ℂ) (w : List (Yau.RIdx n))
    (hi : Integrable (fun x => ‖wordDerivative v w x‖ ^ 2) ((Yau.lebesgueC n).restrict O)) :
    wordEnergy V v w ≤ wordEnergy O v w :=
  integral_mono_measure (Measure.restrict_mono hVO le_rfl)
    (Filter.Eventually.of_forall fun x => sq_nonneg _) hi

theorem evalWordTerms_eq_sum_get (U : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n)) (x : X n) :
    evalWordTerms U L x = ∑ j : Fin L.length, (L.get j).1 x * U (L.get j).2 x := by
  unfold evalWordTerms
  rw [← List.ofFn_getElem_eq_map L (fun t => t.1 x * U t.2 x), List.sum_ofFn]
  simp only [List.get_eq_getElem]

theorem evalWordTerms_norm_sq_le (U : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n)) (x : X n)
    (hc : ∀ t ∈ L, ‖t.1 x‖ ≤ 1) :
    ‖evalWordTerms U L x‖ ^ 2 ≤ (L.length : ℝ) * ∑ j : Fin L.length, ‖U (L.get j).2 x‖ ^ 2 := by
  rw [evalWordTerms_eq_sum_get]
  have hn := norm_sum_le Finset.univ (fun j : Fin L.length => (L.get j).1 x * U (L.get j).2 x)
  have hh := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)).mpr hn
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin L.length => (1 : ℝ))
    (fun j => ‖(L.get j).1 x * U (L.get j).2 x‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hCS
  apply (hh.trans hCS).trans
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hp : ‖(L.get j).1 x * U (L.get j).2 x‖ ≤ ‖U (L.get j).2 x‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hc _ (List.get_mem L j)) (norm_nonneg _)).trans_eq (one_mul _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp

end Yau.LeafProofs.L21Aux
