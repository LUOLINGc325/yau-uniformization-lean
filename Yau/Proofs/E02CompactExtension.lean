import Yau.Proofs.E02CompactNeighborhood
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Filter Function
open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite C² comparison germ has a genuine compactly supported C²
extension on a neighborhood of the whole compact contact set. -/
theorem exists_compact_C2_extension (K U : Set E) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (f : E → ℝ) (hf : ContDiffOn ℝ 2 f U) :
    ∃ (V : Set E) (F : E → ℝ), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ EqOn F f V := by
  obtain ⟨V,hV,hKV,hVC,hVU⟩ := exists_open_precompact_between K U hK hU hKU
  obtain ⟨B,hB,hVB,hBC,hBU⟩ := exists_open_precompact_between (closure V) U hVC hU hVU
  obtain ⟨χ,hχ,_,hSupp,hOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := (2 : ℕ∞))
    hB isClosed_closure hVB
  have hχC : HasCompactSupport χ := by
    change IsCompact (closure (support χ))
    rwa [hSupp]
  have hχU : tsupport χ ⊆ U := by
    simpa only [tsupport,hSupp] using hBU
  have hF : ContDiff ℝ 2 (fun x => χ x*f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hZero : χ =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hxχ => hx (hχU hxχ))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hZero] with y hy
      simp only [hy,Pi.zero_apply,zero_mul]
  refine ⟨V,(fun x => χ x*f x),hV,hKV,(fun x hx => hVU (subset_closure hx)),hF,?_,?_⟩
  · exact hχC.mul_right
  · intro x hx
    change χ x*f x = f x
    rw [(hOne x).mp (subset_closure hx),one_mul]

/-- Compact support and actual C² regularity give a uniform bound on
the actual second Frechet derivative, not on a chosen formal tensor. -/
theorem compact_C2_second_fderiv_bounded (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hC : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨C,hBound⟩ := h1.continuous_fderiv one_ne_zero |>.bounded_above_of_compact_support
    ((hC.fderiv ℝ).fderiv ℝ)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x => ?_⟩
  exact (hBound x).trans (le_max_left _ _)

end Yau.NodeProofs.E02Aux
