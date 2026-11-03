import Yau.LeafProofs.L21WordCorrectionEnergy

/-! Each differentiated classical column equation has a quantitative
ordinary L² output bound involving only the current finite jet of the solution. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem lebesgueC_lt_top_of_isCompact_closure {O : Set (X n)} (hcO : IsCompact (closure O)) :
    Yau.lebesgueC n O < ⊤ := by
  rw [Yau.LeafProofs.lebesgueC_eq_volume]
  exact (measure_mono subset_closure).trans_lt hcO.measure_lt_top

theorem bounded_local_scalar_energy {O : Set (X n)} (hO : IsOpen O) (hcO : IsCompact (closure O))
    (g : X n → ℂ) (hg : ContinuousOn g O) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ x ∈ O, ‖g x‖ ≤ δ) :
    MemLp g 2 ((Yau.lebesgueC n).restrict O) ∧
      (∫ x in O, ‖g x‖ ^ 2 ∂Yau.lebesgueC n) ≤ δ ^ 2 * ∫ x in O, (1 : ℝ) ∂Yau.lebesgueC n := by
  letI : IsFiniteMeasure ((Yau.lebesgueC n).restrict O) :=
    isFiniteMeasure_restrict.mpr (lebesgueC_lt_top_of_isCompact_closure hcO).ne
  have htop : MemLp g ⊤ ((Yau.lebesgueC n).restrict O) := memLp_top_of_bound
    (hg.aestronglyMeasurable hO.measurableSet) δ
    ((ae_restrict_mem hO.measurableSet).mono fun x hx => hb x hx)
  have h2 := htop.mono_exponent (show (2 : ENNReal) ≤ ⊤ by simp)
  refine ⟨h2, ?_⟩
  have hIntC : Integrable (fun _ : X n => δ ^ 2) ((Yau.lebesgueC n).restrict O) := integrable_const _
  have hh := integral_mono_ae (h2.integrable_norm_pow (p := 2) (by decide)) hIntC
    ((ae_restrict_mem hO.measurableSet).mono fun x hx =>
      (sq_le_sq₀ (norm_nonneg _) hδ).mpr (hb x hx))
  apply hh.trans_eq
  rw [← integral_const_mul]
  simp only [mul_one]

theorem column_word_energy_bound {O : Set (X n)} (hO : IsOpen O) (hcO : IsCompact (closure O))
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hJet : JetBound q δ A O)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) (i k : Fin n) :
    MemLp (wordDerivative (fun y => A y i k) w) 2 ((Yau.lebesgueC n).restrict O) ∧
      wordEnergy O (fun y => A y i k) w ≤ δ ^ 2 * ∫ x in O, (1 : ℝ) ∂Yau.lebesgueC n :=
  bounded_local_scalar_energy hO hcO _ (contDiffOn_wordDerivative hO (hA i k) w).continuousOn hδ
    (fun x hx => jetBound_wordDerivative hO hA hJet w hw x hx i k)

theorem graph_word_energy_bound {O : Set (X n)} (hO : IsOpen O) (hcO : IsCompact (closure O))
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hJet : JetBound q 1 A O) (hSmallJet : JetBound q δ A O)
    (v : X n → ℂ) (hv : ContDiff ℝ ∞ v) (k : Fin n)
    (heq : ∀ x ∈ O, ∀ i, dbarA A i v x = A x i k)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ q) (i : Fin n) :
    MemLp (dbarA A i (wordDerivative v w)) 2 ((Yau.lebesgueC n).restrict O) ∧
      (∫ x in O, ‖dbarA A i (wordDerivative v w) x‖ ^ 2 ∂Yau.lebesgueC n) ≤
        2 * δ ^ 2 * (∫ x in O, (1 : ℝ) ∂Yau.lebesgueC n) +
          2 * ((realDimension n : ℝ) * 2 ^ q) ^ 2 * finiteJetEnergy q O v := by
  let a := wordDerivative (fun y => A y i k) w
  let b := evalWordTerms (wordDerivative v) (correctionTerms A i w)
  have ha := column_word_energy_bound hO hcO hA hδ hSmallJet w hw i k
  have hb : MemLp b 2 ((Yau.lebesgueC n).restrict O) := memLp_evalWordTerms_restrict hO
    (wordDerivative v) (correctionTerms A i w)
    (fun t ht => (correctionTerms_smooth hO hA i w t ht).continuousOn)
    (fun t ht x hx => correctionTerms_coefficient_norm_le_one hO hA hJet i w hw t ht x hx)
    (fun t _ => wordDerivative_memLp_restrict hcO hv t.2)
  have hpoint (x : X n) (hx : x ∈ O) : dbarA A i (wordDerivative v w) x = a x + b x :=
    smooth_word_graph_equation hO hA (fun x j => A x j k) (fun j => hA j k) v hv heq w x hx i
  have hAE : dbarA A i (wordDerivative v w) =ᵐ[(Yau.lebesgueC n).restrict O] (fun x => a x + b x) :=
    (ae_restrict_mem hO.measurableSet).mono fun x hx => hpoint x hx
  have hsum : MemLp (fun x => a x + b x) 2 ((Yau.lebesgueC n).restrict O) := ha.1.add hb
  have hd := (memLp_congr_ae hAE).mpr hsum
  refine ⟨hd, ?_⟩
  have hRight : Integrable (fun x => 2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2)
      ((Yau.lebesgueC n).restrict O) :=
    (ha.1.integrable_norm_pow (p := 2) (by decide) |>.const_mul 2).add
      (hb.integrable_norm_pow (p := 2) (by decide) |>.const_mul 2)
  have hh := integral_mono_ae (hd.integrable_norm_pow (p := 2) (by decide)) hRight
    ((ae_restrict_mem hO.measurableSet).mono fun x hx => by
      change ‖dbarA A i (wordDerivative v w) x‖ ^ 2 ≤ 2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2
      rw [hpoint x hx]
      exact norm_add_sq_le_two _ _)
  rw [integral_add (ha.1.integrable_norm_pow (p := 2) (by decide) |>.const_mul 2)
    (hb.integrable_norm_pow (p := 2) (by decide) |>.const_mul 2), integral_const_mul, integral_const_mul] at hh
  have hc := correction_energy_le hO hcO hA hJet v hv w hw i
  apply hh.trans
  have h1 := mul_le_mul_of_nonneg_left ha.2 (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [wordEnergy, a, b, mul_assoc] using add_le_add h1 h2

end Yau.LeafProofs.L21Aux
