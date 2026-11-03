import Yau.LeafProofs.L14LocalizedBundleSystem

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Topology ContDiff
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

theorem exists_model_open_cutoff {n : ℕ} {O K : Set (ComplexVector n)}
    (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O) :
    ∃ η : ComplexVector n → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ O ∧
      (∀ z, η z ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ z ∈ K, η z = 1 ∧ fderiv ℝ η z = 0) := by
  obtain ⟨Ω, hΩ, hKΩ, hΩO, hcΩ⟩ := exists_open_between_and_isCompact_closure hcK hO hKO
  obtain ⟨η, hη, hηrange, hηsupport, hηone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hΩ hcK.isClosed hKΩ
  have hηbounds (z : ComplexVector n) : η z ∈ Set.Icc (0 : ℝ) 1 := hηrange (Set.mem_range_self z)
  refine ⟨η, hη, ?_, ?_, hηbounds, ?_⟩
  · change IsCompact (tsupport η)
    simpa only [tsupport, hηsupport] using hcΩ
  · simpa only [tsupport, hηsupport] using hΩO
  · intro z hz
    have hz1 : η z = 1 := (hηone z).mp hz
    refine ⟨hz1, IsLocalMax.fderiv_eq_zero ?_⟩
    exact Eventually.of_forall fun y => by rw [hz1]; exact (hηbounds y).2

theorem scalar_cutoff_fderiv_eq_of_one_zero {n : ℕ}
    (η : ComplexVector n → ℝ) (f : ComplexVector n → ℂ) (z : ComplexVector n)
    (hη : DifferentiableAt ℝ η z) (hf : DifferentiableAt ℝ f z)
    (hη1 : η z = 1) (hηd : fderiv ℝ η z = 0) :
    fderiv ℝ (fun w => (η w : ℂ) * f w) z = fderiv ℝ f z := by
  have hηC : DifferentiableAt ℝ (fun w => (η w : ℂ)) z := Complex.ofRealCLM.differentiableAt.comp z hη
  have hηCd := (Complex.ofRealCLM.hasFDerivAt.comp z hη.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => (η w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ η z) at hηCd
  rw [hηd, ContinuousLinearMap.comp_zero] at hηCd
  rw [fderiv_fun_mul hηC hf, hηCd, hη1, Complex.ofReal_one]
  simp
  ext v
  change f z * (0 : ℂ) = 0
  exact mul_zero _

theorem complexFormalAdjointTestRow_cutoff_coeff_eq {n : ℕ} {α β ι : Type*} [Fintype ι]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ) (η : ComplexVector n → ℝ)
    (r : β) (c : α) (ψ : ComplexVector n → ℝ) (z : ComplexVector n)
    (hη : DifferentiableAt ℝ η z) (ha : ∀ i, DifferentiableAt ℝ (a r c i) z)
    (hη1 : η z = 1) (hηd : fderiv ℝ η z = 0) :
    complexFormalAdjointTestRow v (fun r c i w => (η w : ℂ) * a r c i w)
      (fun r c w => (η w : ℂ) * b r c w) r c ψ z =
      complexFormalAdjointTestRow v a b r c ψ z := by
  have hd (i : ι) : fderiv ℝ (fun w => (η w : ℂ) * a r c i w) z = fderiv ℝ (a r c i) z :=
    scalar_cutoff_fderiv_eq_of_one_zero η (a r c i) z hη (ha i) hη1 hηd
  unfold complexFormalAdjointTestRow
  simp only [hd, hη1, Complex.ofReal_one, one_mul]

theorem complex_firstOrder_rows_extend_coefficients {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
    {O K : Set (ComplexVector n)} (hO : IsOpen O) (hKO : K ⊆ O)
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) O)
    (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (hsu : ∀ c, tsupport (fun z => u z c) ⊆ K)
    (hrow : ∀ r (ψ : ComplexVector n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, (ψ z : ℂ) * w z r ∂lebesgueC n) =
        ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z ∂lebesgueC n)
    (η : ComplexVector n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηK : ∀ z ∈ K, η z = 1 ∧ fderiv ℝ η z = 0)
    (r : β) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, (ψ z : ℂ) * w z r ∂lebesgueC n) =
      ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v
        (fun r c i z => (η z : ℂ) * a r c i z) (fun r c z => (η z : ℂ) * b r c z) r c ψ z ∂lebesgueC n := by
  rw [hrow r ψ hψ hcψ]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  apply Finset.sum_congr rfl
  intro c _
  by_cases hz : u z c = 0
  · simp only [hz, zero_mul]
  · have hzK : z ∈ K := hsu c (subset_tsupport _ hz)
    rw [complexFormalAdjointTestRow_cutoff_coeff_eq v a b η r c ψ z
      (hη.differentiable (by simp) z)
      (fun i => ((ha r c i).contDiffAt (hO.mem_nhds (hKO hzK))).differentiableAt (by simp))
      (hηK z hzK).1 (hηK z hzK).2]

end Yau.LeafProofs.L14Aux
