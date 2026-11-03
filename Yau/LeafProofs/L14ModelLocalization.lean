import Yau.LeafProofs.L14JointLocalSystem

noncomputable section
open scoped Topology ContDiff
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

theorem compact_complex_cutoff_properties {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ O) (f : ComplexVector n → ℂ) (hf : ContDiffOn ℝ ∞ f O) :
    ContDiff ℝ ∞ (fun z => (χ z : ℂ) * f z) ∧ HasCompactSupport (fun z => (χ z : ℂ) * f z) ∧
      tsupport (fun z => (χ z : ℂ) * f z) ⊆ tsupport χ := by
  have hs : tsupport (fun z => (χ z : ℂ) * f z) ⊆ tsupport χ :=
    tsupport_mul_subset_left.trans (tsupport_comp_subset Complex.ofReal_zero χ)
  exact ⟨contDiff_of_contDiffOn_of_tsupport_subset hO _
    ((Complex.ofRealCLM.contDiff.comp hχ).contDiffOn.mul hf) (hs.trans hsχ),
    hcχ.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩

theorem memLp_compact_multiplier_of_local {n : ℕ} {O : Set (ComplexVector n)}
    (χ f : ComplexVector n → ℂ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    (hf : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → MemLp f 2 ((lebesgueC n).restrict K)) :
    MemLp (fun z => χ z * f z) 2 (lebesgueC n) := by
  have hp := memLp_continuousOn_mul_compact (tsupport χ) hcχ χ f hχ.continuousOn (hf _ hcχ hsχ)
  have hind : (tsupport χ).indicator (fun z => χ z * f z) = (fun z => χ z * f z) :=
    Set.indicator_eq_self.mpr ((Function.support_mul_subset_left _ _).trans (subset_tsupport χ))
  have hi := (memLp_indicator_iff_restrict hcχ.measurableSet.nullMeasurableSet).mpr hp
  simpa only [hind] using hi

theorem locallyIntegrableOn_mul_compactTest {n : ℕ} {O : Set (ComplexVector n)}
    (f ψ : ComplexVector n → ℂ) (hf : LocallyIntegrableOn f O (lebesgueC n))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ O) :
    Integrable (fun z => f z * ψ z) (lebesgueC n) := by
  have hp : IntegrableOn (fun z => f z * ψ z) (tsupport ψ) (lebesgueC n) :=
    (hf.integrableOn_compact_subset hsψ hcψ).mul_continuousOn hψ.continuousOn hcψ
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport ψ))).mp hp

def complexFormalAdjointTestRow {n : ℕ} {α β ι : Type*} [Fintype ι]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ) (r : β) (c : α) (ψ : ComplexVector n → ℝ)
    (z : ComplexVector n) : ℂ :=
  -(∑ i, (a r c i z * (fderiv ℝ ψ z (v i) : ℂ) +
    fderiv ℝ (a r c i) z (v i) * (ψ z : ℂ))) + b r c z * (ψ z : ℂ)

theorem complexFormalAdjointTestRow_contDiffOn {n : ℕ} {α β ι : Type*} [Fintype ι]
    {O : Set (ComplexVector n)} (hO : IsOpen O) (v : ι → ComplexVector n)
    (a : β → α → ι → ComplexVector n → ℂ) (b : β → α → ComplexVector n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) O) (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) O)
    (r : β) (c : α) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiffOn ℝ ∞ (complexFormalAdjointTestRow v a b r c ψ) O := by
  have hψd (i : ι) : ContDiff ℝ ∞ (fun z => (fderiv ℝ ψ z (v i) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hψC : ContDiff ℝ ∞ (fun z => (ψ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have had (i : ι) : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (a r c i) z (v i)) O :=
    ((ha r c i).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  apply ContDiffOn.add
  · apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro i _
    exact ((ha r c i).mul (hψd i).contDiffOn).add ((had i).mul hψC.contDiffOn)
  · exact (hb r c).mul hψC.contDiffOn

theorem complexFormalAdjointTestRow_mul {n : ℕ} {α β ι : Type*} [Fintype ι]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ) (r : β) (c : α)
    (χ ψ : ComplexVector n → ℝ) (z : ComplexVector n)
    (hχ : DifferentiableAt ℝ χ z) (hψ : DifferentiableAt ℝ ψ z) :
    complexFormalAdjointTestRow v a b r c (fun w => χ w * ψ w) z =
      (χ z : ℂ) * complexFormalAdjointTestRow v a b r c ψ z -
        (ψ z : ℂ) * ∑ i, a r c i z * (fderiv ℝ χ z (v i) : ℂ) := by
  have hd (i : ι) : fderiv ℝ (fun w => χ w * ψ w) z (v i) =
      χ z * fderiv ℝ ψ z (v i) + ψ z * fderiv ℝ χ z (v i) := by
    rw [fderiv_fun_mul hχ hψ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsum : (∑ i, (a r c i z * ((χ z : ℂ) * (fderiv ℝ ψ z (v i) : ℂ) +
      (ψ z : ℂ) * (fderiv ℝ χ z (v i) : ℂ)) +
      fderiv ℝ (a r c i) z (v i) * ((χ z : ℂ) * (ψ z : ℂ)))) =
      (χ z : ℂ) * (∑ i, (a r c i z * (fderiv ℝ ψ z (v i) : ℂ) +
        fderiv ℝ (a r c i) z (v i) * (ψ z : ℂ))) +
      (ψ z : ℂ) * ∑ i, a r c i z * (fderiv ℝ χ z (v i) : ℂ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [complexFormalAdjointTestRow, hd, Complex.ofReal_add, Complex.ofReal_mul]
  rw [hsum]
  ring

theorem compact_complex_cutoff_derivative_properties {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ O) (v : ComplexVector n)
    (f : ComplexVector n → ℂ) (hf : ContDiffOn ℝ ∞ f O) :
    ContDiff ℝ ∞ (fun z => (fderiv ℝ χ z v : ℂ) * f z) ∧
      HasCompactSupport (fun z => (fderiv ℝ χ z v : ℂ) * f z) ∧
      tsupport (fun z => (fderiv ℝ χ z v : ℂ) * f z) ⊆ tsupport χ := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hsD : tsupport (fun z => fderiv ℝ χ z v) ⊆ tsupport χ := tsupport_fderiv_apply_subset ℝ v
  obtain ⟨hs, hc, hsub⟩ := compact_complex_cutoff_properties hO _ hd (hcχ.fderiv_apply ℝ v) (hsD.trans hsχ) f hf
  exact ⟨hs, hc, hsub.trans hsD⟩

def localizedComplexSystemOutput {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (χ : ComplexVector n → ℝ) (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (z : ComplexVector n) (r : β) : ℂ :=
  (χ z : ℂ) * w z r + ∑ c, ∑ i, (fderiv ℝ χ z (v i) : ℂ) * a r c i z * u z c

theorem complex_firstOrder_rows_localize {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
    {O : Set (ComplexVector n)} (hO : IsOpen O) (v : ι → ComplexVector n)
    (a : β → α → ι → ComplexVector n → ℂ) (b : β → α → ComplexVector n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) O) (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) O)
    (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (hu : ∀ c, LocallyIntegrableOn (fun z => u z c) O (lebesgueC n))
    (hw : ∀ r, LocallyIntegrableOn (fun z => w z r) O (lebesgueC n))
    (hrow : ∀ r (ψ : ComplexVector n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
      (∫ z, (ψ z : ℂ) * w z r ∂lebesgueC n) =
        ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z ∂lebesgueC n)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    (r : β) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, (ψ z : ℂ) * localizedComplexSystemOutput v a χ u w z r ∂lebesgueC n) =
      ∫ z, ∑ c, ((χ z : ℂ) * u z c) * complexFormalAdjointTestRow v a b r c ψ z ∂lebesgueC n := by
  classical
  let T := fun c z => ((χ z : ℂ) * u z c) * complexFormalAdjointTestRow v a b r c ψ z
  let S := fun c i z => (ψ z : ℂ) * ((fderiv ℝ χ z (v i) : ℂ) * a r c i z * u z c)
  let V := fun z => (ψ z : ℂ) * ((χ z : ℂ) * w z r)
  have hT (c : α) : Integrable (T c) (lebesgueC n) := by
    obtain ⟨hf, hcf, hsf⟩ := compact_complex_cutoff_properties hO χ hχ hcχ hsχ
      (complexFormalAdjointTestRow v a b r c ψ)
      (complexFormalAdjointTestRow_contDiffOn hO v a b ha hb r c ψ hψ)
    have hi := locallyIntegrableOn_mul_compactTest (fun z => u z c) _ (hu c) hf.continuous hcf (hsf.trans hsχ)
    apply hi.congr
    exact Eventually.of_forall fun z => by dsimp only [T]; ring
  have hS (c : α) (i : ι) : Integrable (S c i) (lebesgueC n) := by
    obtain ⟨hd, hcd, hsd⟩ := compact_complex_cutoff_derivative_properties hO χ hχ hcχ hsχ (v i)
      (a r c i) (ha r c i)
    let f := fun z => (ψ z : ℂ) * ((fderiv ℝ χ z (v i) : ℂ) * a r c i z)
    have hf : ContDiff ℝ ∞ f := (Complex.ofRealCLM.contDiff.comp hψ).mul hd
    have hcf : HasCompactSupport f := hcd.mul_left
    have hsf : tsupport f ⊆ O := tsupport_mul_subset_right.trans (hsd.trans hsχ)
    have hi := locallyIntegrableOn_mul_compactTest (fun z => u z c) f (hu c) hf.continuous hcf hsf
    apply hi.congr
    exact Eventually.of_forall fun z => by dsimp only [S, f]; ring
  have hV : Integrable V (lebesgueC n) := by
    let f := fun z => Complex.ofReal (ψ z * χ z)
    have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp (hψ.mul hχ)
    have hcf : HasCompactSupport f := hcχ.mul_left.comp_left Complex.ofReal_zero
    have hsf : tsupport f ⊆ O := (tsupport_comp_subset Complex.ofReal_zero _).trans
      (tsupport_mul_subset_right.trans hsχ)
    have hi := locallyIntegrableOn_mul_compactTest (fun z => w z r) f (hw r) hf.continuous hcf hsf
    apply hi.congr
    exact Eventually.of_forall fun z => by dsimp only [V, f]; push_cast; ring
  have hTs : Integrable (fun z => ∑ c, T c z) (lebesgueC n) := integrable_finsetSum _ (fun c _ => hT c)
  have hSs : Integrable (fun z => ∑ c, ∑ i, S c i z) (lebesgueC n) :=
    integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun i _ => hS c i))
  have hp (c : α) (z : ComplexVector n) :
      u z c * complexFormalAdjointTestRow v a b r c (fun y => χ y * ψ y) z = T c z - ∑ i, S c i z := by
    rw [complexFormalAdjointTestRow_mul v a b r c χ ψ z
      (hχ.differentiable (by simp) z) (hψ.differentiable (by simp) z)]
    calc
      _ = T c z - ∑ i, u z c * ((ψ z : ℂ) * (a r c i z * (fderiv ℝ χ z (v i) : ℂ))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        dsimp only [T]
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [S]
        ring
  have heq : (∫ z, V z ∂lebesgueC n) =
      (∫ z, ∑ c, T c z ∂lebesgueC n) - (∫ z, ∑ c, ∑ i, S c i z ∂lebesgueC n) := by
    calc
      _ = ∫ z, ((χ z * ψ z : ℝ) : ℂ) * w z r ∂lebesgueC n :=
        integral_congr_ae (Eventually.of_forall fun z => by dsimp only [V]; push_cast; ring)
      _ = ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v a b r c (fun y => χ y * ψ y) z ∂lebesgueC n :=
        hrow r _ (hχ.mul hψ) hcχ.mul_right (tsupport_mul_subset_left.trans hsχ)
      _ = ∫ z, (∑ c, T c z) - ∑ c, ∑ i, S c i z ∂lebesgueC n := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by simp only [hp, Finset.sum_sub_distrib]
      _ = _ := integral_sub hTs hSs
  calc
    _ = ∫ z, V z + ∑ c, ∑ i, S c i z ∂lebesgueC n := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [localizedComplexSystemOutput, V, S]
        simp only [mul_add, Finset.mul_sum]
    _ = (∫ z, V z ∂lebesgueC n) + (∫ z, ∑ c, ∑ i, S c i z ∂lebesgueC n) := integral_add hV hSs
    _ = ∫ z, ∑ c, T c z ∂lebesgueC n := by rw [heq]; ring
    _ = _ := rfl

theorem localizedComplexSystemOutput_tsupport_subset {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (χ : ComplexVector n → ℝ) (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ) (r : β) :
    tsupport (fun z => localizedComplexSystemOutput v a χ u w z r) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra hn
  have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport hn
  have hdχ : fderiv ℝ χ z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  apply hz
  simp only [localizedComplexSystemOutput, hχz, hdχ, ContinuousLinearMap.zero_apply,
    Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, zero_add]

theorem localizedComplexSystemInput_memLp {n : ℕ} {O : Set (ComplexVector n)}
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    (u : ComplexVector n → ℂ)
    (hu : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → MemLp u 2 ((lebesgueC n).restrict K)) :
    MemLp (fun z => (χ z : ℂ) * u z) 2 (lebesgueC n) :=
  memLp_compact_multiplier_of_local _ u (Complex.continuous_ofReal.comp hχ.continuous)
    (hcχ.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ) hu

theorem localizedComplexSystemOutput_memLp {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
    {O : Set (ComplexVector n)} (hO : IsOpen O) (v : ι → ComplexVector n)
    (a : β → α → ι → ComplexVector n → ℂ) (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) O)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (hu : ∀ c (K : Set (ComplexVector n)), IsCompact K → K ⊆ O →
      MemLp (fun z => u z c) 2 ((lebesgueC n).restrict K))
    (hw : ∀ r (K : Set (ComplexVector n)), IsCompact K → K ⊆ O →
      MemLp (fun z => w z r) 2 ((lebesgueC n).restrict K)) (r : β) :
    MemLp (fun z => localizedComplexSystemOutput v a χ u w z r) 2 (lebesgueC n) := by
  have hbase := localizedComplexSystemInput_memLp χ hχ hcχ hsχ (fun z => w z r) (hw r)
  have hterm (c : α) (i : ι) : MemLp (fun z => (fderiv ℝ χ z (v i) : ℂ) * a r c i z * u z c) 2 (lebesgueC n) := by
    obtain ⟨hf, hcf, hsf⟩ := compact_complex_cutoff_derivative_properties hO χ hχ hcχ hsχ (v i) (a r c i) (ha r c i)
    exact memLp_compact_multiplier_of_local _ _ hf.continuous hcf (hsf.trans hsχ) (hu c)
  have hs : MemLp (fun z => ∑ c, ∑ i, (fderiv ℝ χ z (v i) : ℂ) * a r c i z * u z c) 2 (lebesgueC n) := by
    exact memLp_finsetSum Finset.univ (fun c _ => memLp_finsetSum Finset.univ (fun i _ => hterm c i))
  exact hbase.add hs

end Yau.LeafProofs.L14Aux
