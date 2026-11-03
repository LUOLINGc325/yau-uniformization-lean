import Yau.Proofs.P06SmallTimeCylinderScaling
import Yau.Proofs.P06CylinderRegularityJointEstimate

/-! Quantitative cutoff word calculus retains the actual ordered Leibniz
splits, including their multiplicities. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.LeafProofs.L16Aux CylinderReg

section Lists
variable {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem listSum_contDiff (s : List β) (f : β → E → ℝ)
    (hf : ∀ b, ContDiff ℝ ∞ (f b)) :
    ContDiff ℝ ∞ (fun p => (s.map (fun b => f b p)).sum) := by
  induction s with
  | nil => exact contDiff_const
  | cons b s ih => exact (hf b).add ih

theorem direction_listSum (s : List β) (f : β → E → ℝ)
    (hf : ∀ b, ContDiff ℝ ∞ (f b)) (v : E) :
    regularityDirection v (fun p => (s.map (fun b => f b p)).sum) =
      fun p => (s.map (fun b => regularityDirection v (f b) p)).sum := by
  induction s with
  | nil => funext p; simp [regularityDirection]
  | cons b s ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [regularityDirection_add (hf b) (listSum_contDiff s f hf) v, ih]

theorem list_sum_map_eq_sum_get (s : List β) (f : β → ℝ) :
    (s.map f).sum = ∑ i : Fin s.length, f (s.get i) := by
  calc
    _ = ((List.ofFn (fun i : Fin s.length => s.get i)).map f).sum := by
      rw [List.ofFn_get]
    _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl

theorem list_sum_sq_le (s : List β) (f : β → ℝ) :
    (s.map f).sum ^ 2 ≤ (s.length : ℝ) * (s.map (fun b => (f b) ^ 2)).sum := by
  rw [list_sum_map_eq_sum_get, list_sum_map_eq_sum_get]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin s.length => (1 : ℝ)) (fun i => f (s.get i))
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using h

theorem listSum_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : List β) (f : β → X → ℝ) (hf : ∀ b, Integrable (f b) μ) :
    Integrable (fun p => (s.map (fun b => f b p)).sum) μ := by
  induction s with
  | nil => exact integrable_zero X ℝ μ
  | cons b s ih => exact (hf b).add ih

theorem integral_listSum {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : List β) (f : β → X → ℝ) (hf : ∀ b, Integrable (f b) μ) :
    (∫ p, (s.map (fun b => f b p)).sum ∂μ) = (s.map (fun b => ∫ p, f b p ∂μ)).sum := by
  induction s with
  | nil => simp
  | cons b s ih =>
    have hInt := listSum_integrable μ s f hf
    simpa only [List.map_cons, List.sum_cons, integral_add (hf b) hInt] using
      congrArg (fun x => (∫ p, f b p ∂μ) + x) ih

end Lists

theorem word_mul {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ι → E) {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List ι) (p : E) :
    regularityCoefficientWord v w (fun p => f p * g p) p =
      ((regularityWordSplits w).map (fun st =>
        regularityCoefficientWord v st.1 f p * regularityCoefficientWord v st.2 g p)).sum := by
  induction w generalizing p with
  | nil => simp [regularityCoefficientWord, regularityWordSplits]
  | cons j w ih =>
    have he : regularityCoefficientWord v w (fun p => f p * g p) =
        fun p => ((regularityWordSplits w).map (fun st =>
          regularityCoefficientWord v st.1 f p * regularityCoefficientWord v st.2 g p)).sum :=
      funext ih
    change regularityDirection (v j) (regularityCoefficientWord v w (fun p => f p * g p)) p =
      regularityLeibnizJet v f (fun w p (_ : Unit) => regularityCoefficientWord v w g p) (j::w) p ()
    rw [he, direction_listSum (regularityWordSplits w)
      (fun (st : List ι × List ι) p =>
        regularityCoefficientWord v st.1 f p * regularityCoefficientWord v st.2 g p)
      (fun st =>
      (regularityCoefficientWord_contDiff v hf st.1).mul
        (regularityCoefficientWord_contDiff v hg st.2)) (v j), regularityLeibnizJet_cons]
    apply congrArg List.sum
    apply List.map_congr_left
    intro st _
    exact congrFun (regularityDirection_mul
      (regularityCoefficientWord_contDiff v hf st.1)
      (regularityCoefficientWord_contDiff v hg st.2) (v j)) p

theorem word_comp_eigen {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ι → E) (T : E →L[ℝ] E) (a : ι → ℝ) (hT : ∀ i, T (v i) = a i • v i)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (w : List ι) :
    regularityCoefficientWord v w (f ∘ T) =
      fun p => (w.map a).prod * regularityCoefficientWord v w f (T p) := by
  induction w with
  | nil => funext p; simp [regularityCoefficientWord]
  | cons j w ih =>
    funext p
    have hW := regularityCoefficientWord_contDiff v hf w
    have hComp : ContDiff ℝ ∞ (regularityCoefficientWord v w f ∘ T) :=
      hW.comp T.contDiff
    change fderiv ℝ (regularityCoefficientWord v w (f ∘ T)) p (v j) = _
    rw [ih]
    have hdf : HasFDerivAt
        (fun p => (w.map a).prod * regularityCoefficientWord v w f (T p))
        ((w.map a).prod • (fderiv ℝ (regularityCoefficientWord v w f) (T p)).comp T) p :=
      ((hW.differentiable (by simp) (T p)).hasFDerivAt.comp p T.hasFDerivAt).const_mul _
    rw [hdf.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, hT,
      map_smul, List.map_cons, List.prod_cons, regularityCoefficientWord,
      regularityDirection]
    ring

def timeWeight {n : ℕ} (τ : ℝ) : ParabolicJointIdx n → ℝ
  | .inl _ => 1
  | .inr _ => 1 / τ

theorem timeScale_symm_jointVec {n : ℕ} (τ : ℝ) (hτ : τ ≠ 0)
    (i : ParabolicJointIdx n) :
    (timeScale τ hτ).symm.toContinuousLinearMap (parabolicJointVec i) =
      timeWeight τ i • parabolicJointVec i := by
  cases i <;> simp [parabolicJointVec, timeWeight, smul_eq_mul]

theorem timeWeight_prod_bounds {n : ℕ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (w : List (ParabolicJointIdx n)) :
    0 ≤ (w.map (timeWeight τ)).prod ∧
      (w.map (timeWeight τ)).prod ≤ (1 / τ) ^ w.length := by
  have ha (i : ParabolicJointIdx n) : 0 ≤ timeWeight τ i ∧ timeWeight τ i ≤ 1 / τ := by
    cases i with
    | inl i => exact ⟨zero_le_one, (one_le_div hτ).mpr hτ1⟩
    | inr i => exact ⟨div_nonneg zero_le_one hτ.le, le_rfl⟩
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    exact ⟨mul_nonneg (ha j).1 ih.1,
      (mul_le_mul (ha j).2 ih.2 ih.1 (by positivity)).trans_eq (mul_comm _ _)⟩

theorem exists_rescaleProfile_word_bound {n : ℕ} {χ : Point n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (w : List (ParabolicJointIdx n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 → ∀ p,
      |regularityCoefficientWord parabolicJointVec w (rescaleProfile τ hτ.ne' χ) p| ≤
        C / τ ^ w.length := by
  have hr := regularityCoefficientWord_regular parabolicJointVec hχ hcχ w
  obtain ⟨b, hb⟩ := hr.1.continuous.bounded_above_of_compact_support hr.2.1
  let C := max b 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 p
  have he := word_comp_eigen parabolicJointVec
    (timeScale τ hτ.ne').symm.toContinuousLinearMap (timeWeight τ)
    (timeScale_symm_jointVec τ hτ.ne') hχ w
  have hp := timeWeight_prod_bounds hτ hτ1 w
  have hb' : |regularityCoefficientWord parabolicJointVec w χ
      ((timeScale τ hτ.ne').symm p)| ≤ C := by
    simpa only [Real.norm_eq_abs] using (hb _).trans (le_max_left b 0)
  change |regularityCoefficientWord parabolicJointVec w
    (χ ∘ (timeScale τ hτ.ne').symm.toContinuousLinearMap) p| ≤ _
  rw [congrFun he p, abs_mul, abs_of_nonneg hp.1]
  calc
    _ ≤ ((w.map (timeWeight τ)).prod) * C := mul_le_mul_of_nonneg_left hb' hp.1
    _ ≤ (1 / τ) ^ w.length * C := mul_le_mul_of_nonneg_right hp.2 hC
    _ = _ := by simp only [div_eq_mul_inv, one_mul, inv_pow]; ring

def dilationHull {n : ℕ} (K : Set (Point n)) : Set (Point n) :=
  (fun p : ℝ × Point n => (p.2.1, p.1 * p.2.2)) '' (Set.Icc 0 1 ×ˢ K)

theorem dilationHull_isCompact {n : ℕ} {K : Set (Point n)} (hK : IsCompact K) :
    IsCompact (dilationHull K) :=
  (isCompact_Icc.prod hK).image (by fun_prop)

theorem timeScale_image_subset_dilationHull {n : ℕ} {K : Set (Point n)}
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    timeScale τ hτ.ne' '' K ⊆ dilationHull K := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨(τ,p), ⟨⟨hτ.le,hτ1⟩,hp⟩,rfl⟩

end Yau.NodeProofs.P06Aux.SmallTimeCylinder
