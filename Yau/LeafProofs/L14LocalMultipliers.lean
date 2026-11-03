import Yau.LeafProofs.L14ModelL2

noncomputable section
open scoped Topology ContDiff
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

theorem memLp_compact_local_mul {n : ℕ}
    {O K : Set (ComplexVector n)} (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O)
    (f : ComplexVector n → ℂ) (hf : MemLp f 2 (lebesgueC n)) (hsf : tsupport f ⊆ K)
    (c : ComplexVector n → ℂ) (hc : ContDiffOn ℝ ∞ c O) :
    MemLp (fun z => c z * f z) 2 (lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  obtain ⟨η, hη, hcη, hsη, _, hηK⟩ := exists_model_open_cutoff hO hcK hKO
  obtain ⟨hC, hcC, _⟩ := compact_complex_cutoff_properties hO η hη hcη hsη c hc
  have hmC : MemLp (fun z => (η z : ℂ) * c z) ⊤ (lebesgueC n) :=
    hC.continuous.memLp_of_hasCompactSupport hcC
  apply (hmC.mul hf).ae_eq
  apply Eventually.of_forall
  intro z
  change ((η z : ℂ) * c z) * f z = c z * f z
  by_cases hz : f z = 0
  · simp only [hz, mul_zero]
  · simp only [(hηK z (hsf (subset_tsupport _ hz))).1, Complex.ofReal_one, one_mul]

/-- A smooth local coefficient preserves strong L² errors supported in one
fixed compact subset of its genuine open domain. -/
theorem integral_sq_tendsto_zero_compact_local_mul {n : ℕ}
    {O K : Set (ComplexVector n)} (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O)
    (f : ℕ → ComplexVector n → ℂ) (hf : ∀ j, MemLp (f j) 2 (lebesgueC n))
    (hsf : ∀ j, tsupport (f j) ⊆ K)
    (ht : Tendsto (fun j => ∫ z, ‖f j z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0))
    (c : ComplexVector n → ℂ) (hc : ContDiffOn ℝ ∞ c O) :
    (∀ j, MemLp (fun z => c z * f j z) 2 (lebesgueC n)) ∧
      Tendsto (fun j => ∫ z, ‖c z * f j z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
  obtain ⟨η, hη, hcη, hsη, _, hηK⟩ := exists_model_open_cutoff hO hcK hKO
  let C := fun z => (η z : ℂ) * c z
  obtain ⟨hC, hcC, _⟩ := compact_complex_cutoff_properties hO η hη hcη hsη c hc
  obtain ⟨B, hB⟩ := hC.continuous.bounded_above_of_compact_support hcC
  have he (j : ℕ) : (fun z => C z * f j z) = fun z => c z * f j z := by
    funext z
    by_cases hz : f j z = 0
    · simp only [hz, mul_zero]
    · have hzK : z ∈ K := hsf j (subset_tsupport _ hz)
      simp only [C, (hηK z hzK).1, Complex.ofReal_one, one_mul]
  have heval (j : ℕ) (z : ComplexVector n) : C z * f j z = c z * f j z := congrFun (he j) z
  simpa only [heval] using integral_sq_tendsto_zero_bounded_complex_mul (lebesgueC n) f hf ht C
    hC.continuous.aestronglyMeasurable (max B 0) (le_max_right _ _)
    (fun z => (hB z).trans (le_max_left _ _))

/-- Finite smooth matrix transformations preserve the same compact model
graph limits. This applies in particular to the inverse weighted bundle metric. -/
theorem integral_sq_tendsto_zero_compact_local_matrix {n : ℕ} {α β : Type*} [Fintype α]
    {O K : Set (ComplexVector n)} (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O)
    (f : ℕ → ComplexVector n → α → ℂ)
    (hf : ∀ j c, MemLp (fun z => f j z c) 2 (lebesgueC n))
    (hsf : ∀ j c, tsupport (fun z => f j z c) ⊆ K)
    (ht : ∀ c, Tendsto (fun j => ∫ z, ‖f j z c‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0))
    (A : β → α → ComplexVector n → ℂ) (hA : ∀ r c, ContDiffOn ℝ ∞ (A r c) O)
    (r : β) :
    (∀ j, MemLp (fun z => ∑ c, A r c z * f j z c) 2 (lebesgueC n)) ∧
      Tendsto (fun j => ∫ z, ‖∑ c, A r c z * f j z c‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
  have he (c : α) := integral_sq_tendsto_zero_compact_local_mul hO hcK hKO
    (fun j z => f j z c) (fun j => hf j c) (fun j => hsf j c) (ht c) (A r c) (hA r c)
  exact Yau.LeafProofs.L03.integral_sq_tendsto_zero_fintype_sum (lebesgueC n)
    (fun j z c => A r c z * f j z c) (fun j c => (he c).1 j) (fun c => (he c).2)

end Yau.LeafProofs.L14Aux
