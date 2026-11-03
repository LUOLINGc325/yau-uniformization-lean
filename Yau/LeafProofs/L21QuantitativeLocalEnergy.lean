import Yau.LeafProofs.L21QuantitativeCutoffs

/-! A fixed pair of inner domains has a first-order energy constant chosen
before the graph coefficients and the smooth solution. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem local_gradient_energy_cutoff_bound {O R : Set (X n)} (hO : IsOpen O) (hR : MeasurableSet R)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (hAbound : ∀ x ∈ O, ∀ i j, ‖A x i j‖ ≤ 1)
    (χ : X n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    (hχrange : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχR : ∀ x ∈ R, χ x = 1 ∧ fderiv ℝ χ x = 0)
    {L : ℝ} (hL : 0 ≤ L) (hχL : ∀ x (a : Yau.RIdx n), ‖fderiv ℝ χ x (Yau.realVec a)‖ ≤ L)
    (v : X n → ℂ) (hv : ContDiff ℝ ∞ v)
    (hv2 : MemLp v 2 ((Yau.lebesgueC n).restrict O))
    (hDv2 : ∀ i, MemLp (dbarA A i v) 2 ((Yau.lebesgueC n).restrict O)) :
    (∑ a : Yau.RIdx n, ∫ x in R, ‖fderiv ℝ v x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n) ≤
      32 * ((∑ i : Fin n, ∫ x in O, ‖dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) +
        (n : ℝ) * ((realDimension n : ℝ) * L) ^ 2 * ∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let u := cutoffTest χ hχ hcχ hsχ v hv
  let χC := ofRealTest χ hχ hcχ hsχ
  have hχCsmooth : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hInt1 (i : Fin n) : Integrable (fun x => ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2) (Yau.lebesgueC n) := by
    obtain ⟨hh, hc, _⟩ := Yau.LeafProofs.L14Aux.compact_complex_cutoff_properties
      hO χ hχ hcχ hsχ (dbarA A i v) (contDiffOn_dbarA hO hA i hv.contDiffOn)
    exact (hh.continuous.memLp_of_hasCompactSupport hc).integrable_norm_pow (p := 2) (by decide)
  have hInt2 (i : Fin n) : Integrable (fun x => ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2)
      (Yau.lebesgueC n) := by
    let g := testD hO hA i χC
    exact ((hv.mul g.property.1).continuous.memLp_of_hasCompactSupport g.property.2.1.mul_left).integrable_norm_pow
      (p := 2) (by decide)
  have hM1 (i : Fin n) : (∫ x, ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) ≤
      ∫ x in O, ‖dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n := by
    have hb (x : X n) : ‖(χ x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
      exact (hχrange x).2
    simpa only [one_pow, one_mul] using integral_compact_multiplier_norm_sq_le
      (fun x => (χ x : ℂ)) (dbarA A i v) (C := 1) (by norm_num) hb
      ((tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ) (hInt1 i)
      ((hDv2 i).integrable_norm_pow (p := 2) (by decide))
  have hM2 (i : Fin n) : (∫ x, ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2 ∂Yau.lebesgueC n) ≤
      ((realDimension n : ℝ) * L) ^ 2 * ∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n := by
    have hp : Integrable (fun x => ‖dbarA A i (fun y => (χ y : ℂ)) x * v x‖ ^ 2) (Yau.lebesgueC n) := by
      simpa only [mul_comm] using hInt2 i
    have hh := integral_compact_multiplier_norm_sq_le (dbarA A i (fun y => (χ y : ℂ))) v
      (by positivity : 0 ≤ (realDimension n : ℝ) * L)
      (dbarA_ofReal_cutoff_bound A hAbound hχ hsχ hL hχL i)
      ((tsupport_dbarA_subset A i _).trans ((tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ))
      hp (hv2.integrable_norm_pow (p := 2) (by decide))
    simpa only [mul_comm] using hh
  have hLower : (∑ a : Yau.RIdx n, ∫ x in R, ‖fderiv ℝ v x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n) ≤
      ∑ a : Yau.RIdx n, ∫ x, ‖fderiv ℝ u x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n := by
    apply Finset.sum_le_sum
    intro a _
    have he : (∫ x in R, ‖fderiv ℝ v x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n) =
        ∫ x in R, ‖fderiv ℝ u x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hR] with x hx
      apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
      change fderiv ℝ v x (Yau.realVec a) =
        fderiv ℝ (fun y => (χ y : ℂ) * v y) x (Yau.realVec a)
      rw [fderiv_fun_mul (c := fun y => (χ y : ℂ)) (d := v)
        (hχCsmooth.differentiable (by simp) x) (hv.differentiable (by simp) x)]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
        fderiv_ofReal_apply (hχ.differentiable (by simp) x), (hχR x hx).1, (hχR x hx).2,
        _root_.zero_apply, Complex.ofReal_zero, Complex.ofReal_one, mul_zero, add_zero, one_mul]
    rw [he]
    exact setIntegral_le_integral
      (integrable_directional_norm_sq u.property.1 u.property.2.1 (Yau.realVec a))
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hSum1 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hM1 i)
  have hSum2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hM2 i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hSum2
  calc
    _ ≤ ∑ a : Yau.RIdx n, ∫ x, ‖fderiv ℝ u x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n := hLower
    _ ≤ 32 * ((∑ i : Fin n, ∫ x, ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) +
        ∑ i : Fin n, ∫ x, ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2 ∂Yau.lebesgueC n) :=
      cutoff_compact_gradient_energy hO hA hsmall χ hχ hcχ hsχ v hv
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (add_le_add hSum1 hSum2) (by norm_num : (0 : ℝ) ≤ 32)
      simpa only [mul_assoc] using hh

theorem exists_inner_gradient_energy_bound {O R : Set (X n)} (hO : IsOpen O) (hR : IsOpen R)
    (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A O →
      (∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) → JetBound 0 1 A O →
      ∀ (v : X n → ℂ), ContDiff ℝ ∞ v → MemLp v 2 ((Yau.lebesgueC n).restrict O) →
      (∀ i, MemLp (dbarA A i v) 2 ((Yau.lebesgueC n).restrict O)) →
      (∑ a : Yau.RIdx n, ∫ x in R, ‖fderiv ℝ v x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n) ≤
        C * ((∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) +
          ∑ i : Fin n, ∫ x in O, ‖dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) := by
  obtain ⟨χ, hχ, hcχ, hsχ, hχrange, hχR⟩ := Yau.LeafProofs.L14Aux.exists_model_open_cutoff hO hcR hRO
  obtain ⟨L, hL, hχL⟩ := exists_cutoff_directional_bound hχ hcχ
  let b := (n : ℝ) * ((realDimension n : ℝ) * L) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨32 * (1 + b), by positivity, ?_⟩
  intro A hA hsmall hJet v hv hv2 hDv2
  have hAbound (x : X n) (hx : x ∈ O) (i j : Fin n) : ‖A x i j‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_zero] using hJet 0 le_rfl x hx i j
  have hh := local_gradient_energy_cutoff_bound hO hR.measurableSet hA hsmall hAbound
    χ hχ hcχ hsχ hχrange (fun x hx => hχR x (subset_closure hx)) hL.le hχL v hv hv2 hDv2
  apply hh.trans
  have hU : 0 ≤ ∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n := integral_nonneg fun x => sq_nonneg _
  have hD : 0 ≤ ∑ i : Fin n, ∫ x in O, ‖dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  change 32 * ((∑ i, ∫ x in O, ‖dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) +
    b * ∫ x in O, ‖v x‖ ^ 2 ∂Yau.lebesgueC n) ≤ _
  nlinarith [mul_nonneg hb hD]

end Yau.LeafProofs.L21Aux
