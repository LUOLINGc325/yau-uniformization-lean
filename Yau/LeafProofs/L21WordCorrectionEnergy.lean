import Yau.LeafProofs.L21SmoothWordEquation

/-! The correction part of each actual differentiated equation has a
uniform L² bound in the previous finite jet energy. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem memLp_evalWordTerms_restrict {O : Set (X n)} (hO : IsOpen O)
    (U : List (Yau.RIdx n) → X n → ℂ) (L : List (WordTerm n))
    (hc : ∀ t ∈ L, ContinuousOn t.1 O)
    (hb : ∀ t ∈ L, ∀ x ∈ O, ‖t.1 x‖ ≤ 1)
    (hU : ∀ t ∈ L, MemLp (U t.2) 2 ((Yau.lebesgueC n).restrict O)) :
    MemLp (evalWordTerms U L) 2 ((Yau.lebesgueC n).restrict O) := by
  have ht (j : Fin L.length) : MemLp
      (fun x => (L.get j).1 x * U (L.get j).2 x) 2 ((Yau.lebesgueC n).restrict O) := by
    have hcoeff : MemLp (L.get j).1 ⊤ ((Yau.lebesgueC n).restrict O) := memLp_top_of_bound
      ((hc _ (List.get_mem L j)).aestronglyMeasurable hO.measurableSet) 1
      ((ae_restrict_mem hO.measurableSet).mono fun x hx => hb _ (List.get_mem L j) x hx)
    exact hcoeff.mul (hU _ (List.get_mem L j))
  have hh := memLp_finsetSum Finset.univ (fun j (_ : j ∈ (Finset.univ : Finset (Fin L.length))) => ht j)
  convert! hh using 1
  funext x
  exact evalWordTerms_eq_sum_get U L x

theorem evalWordTerms_energy_le_finiteJetEnergy {O : Set (X n)} (hO : IsOpen O)
    (hcO : IsCompact (closure O)) (q : ℕ) (v : X n → ℂ) (hv : ContDiff ℝ ∞ v)
    (L : List (WordTerm n)) (hc : ∀ t ∈ L, ContinuousOn t.1 O)
    (hb : ∀ t ∈ L, ∀ x ∈ O, ‖t.1 x‖ ≤ 1) (horder : ∀ t ∈ L, t.2.length ≤ q) :
    (∫ x in O, ‖evalWordTerms (wordDerivative v) L x‖ ^ 2 ∂Yau.lebesgueC n) ≤
      (L.length : ℝ) ^ 2 * finiteJetEnergy q O v := by
  have hM := memLp_evalWordTerms_restrict hO (wordDerivative v) L hc hb
    (fun t _ => wordDerivative_memLp_restrict hcO hv t.2)
  have hi (j : Fin L.length) : Integrable
      (fun x => ‖wordDerivative v (L.get j).2 x‖ ^ 2) ((Yau.lebesgueC n).restrict O) :=
    (wordDerivative_memLp_restrict hcO hv _).integrable_norm_pow (p := 2) (by decide)
  have hRight : Integrable (fun x => (L.length : ℝ) *
      ∑ j : Fin L.length, ‖wordDerivative v (L.get j).2 x‖ ^ 2) ((Yau.lebesgueC n).restrict O) :=
    (integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul _
  have hh := integral_mono_ae (hM.integrable_norm_pow (p := 2) (by decide)) hRight
    ((ae_restrict_mem hO.measurableSet).mono fun x hx =>
      evalWordTerms_norm_sq_le (wordDerivative v) L x (fun t ht => hb t ht x hx))
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)] at hh
  have hs : (∑ j : Fin L.length, wordEnergy O v (L.get j).2) ≤
      (L.length : ℝ) * finiteJetEnergy q O v := by
    calc
      _ ≤ ∑ _j : Fin L.length, finiteJetEnergy q O v := Finset.sum_le_sum fun j _ =>
        wordEnergy_le_finiteJetEnergy q O v _ (horder _ (List.get_mem L j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)).trans_eq (by ring)

theorem correctionTerms_length_le (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (q : ℕ) (w : List (Yau.RIdx n)) (hw : w.length ≤ q) :
    (correctionTerms A i w).length ≤ realDimension n * 2 ^ q := by
  have hh := correctionTerms_length_add A i w
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  exact (Nat.le_add_right _ _).trans (hh.le.trans (Nat.mul_le_mul_left _ hp))

theorem correction_energy_le {O : Set (X n)} (hO : IsOpen O) (hcO : IsCompact (closure O))
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {q : ℕ} (hJet : JetBound q 1 A O) (v : X n → ℂ) (hv : ContDiff ℝ ∞ v)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) (i : Fin n) :
    (∫ x in O, ‖evalWordTerms (wordDerivative v) (correctionTerms A i w) x‖ ^ 2 ∂Yau.lebesgueC n) ≤
      ((realDimension n : ℝ) * 2 ^ q) ^ 2 * finiteJetEnergy q O v := by
  apply (evalWordTerms_energy_le_finiteJetEnergy hO hcO q v hv (correctionTerms A i w)
    (fun t ht => (correctionTerms_smooth hO hA i w t ht).continuousOn)
    (fun t ht x hx => correctionTerms_coefficient_norm_le_one hO hA hJet i w hw t ht x hx)
    (fun t ht => (correctionTerms_order A i w t ht).trans hw)).trans
  apply mul_le_mul_of_nonneg_right ?_ (finiteJetEnergy_nonneg q O v)
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr
  exact_mod_cast correctionTerms_length_le A i q w hw

end Yau.LeafProofs.L21Aux
