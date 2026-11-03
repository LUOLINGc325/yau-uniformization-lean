import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Geometry.Manifold.PartitionOfUnity

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- A compact subset of an open planar domain admits a smooth cutoff whose
whole closed support remains in the domain. -/
theorem exists_smooth_cutoff {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z ∈ K, χ z = 1) := by
  obtain ⟨V, hVo, hKV, hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨W, hWo, hKW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  let O := V ∩ W
  have hKO : K ⊆ O := fun z hz ↦ ⟨hKV hz, hKW hz⟩
  obtain ⟨χ, hχ, hχrange, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (hVo.inter hWo) hK.isClosed hKO
  have hts : tsupport χ = closure O := by rw [tsupport, hχsupp]
  refine ⟨χ, hχ, ?_, ?_, fun z ↦ hχrange ⟨z, rfl⟩, fun z hz ↦ (hχone z).mp hz⟩
  · rw [HasCompactSupport, hts]
    exact hWc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_right)
  · rw [hts]
    exact (closure_mono inter_subset_left).trans hVU

/-- Continuous compactly supported planar tests have smooth approximants with
all supports contained in one compact subset of the prescribed domain. -/
theorem exists_smooth_approx {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ tsupport f ⊆ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ g : ℂ → ℝ,
        ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ K ∧
          ∀ z, |g z - f z| ≤ ε := by
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχone⟩ := exists_smooth_cutoff hU hfc hfU
  refine ⟨tsupport χ, hχc, hχU, ?_, ?_⟩
  · intro z hz
    apply subset_tsupport χ
    rw [Function.mem_support, hχone z hz]
    exact one_ne_zero
  · intro ε hε
    obtain ⟨g, hg, hgf⟩ := hf.uniformContinuous_of_tendsto_cocompact hfc.is_zero_at_infty
      |>.exists_contDiff_dist_le hε
    refine ⟨fun z ↦ χ z * g z, hχ.mul hg, hχc.mul_right, ?_, ?_⟩
    · exact tsupport_mul_subset_left
    · intro z
      have heq : χ z * f z = f z := by
        by_cases hz : z ∈ tsupport f
        · rw [hχone z hz, one_mul]
        · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
      calc
        |χ z * g z - f z| = |χ z * (g z - f z)| := by rw [mul_sub, heq]
        _ = |χ z| * |g z - f z| := abs_mul _ _
        _ ≤ 1 * ε := mul_le_mul (by simpa [abs_of_nonneg (hχ01 z).1] using (hχ01 z).2)
          (by simpa [Real.dist_eq] using (hgf z).le) (abs_nonneg _) zero_le_one
        _ = ε := one_mul _

end Yau.NodeProofs.D02RieszAux
