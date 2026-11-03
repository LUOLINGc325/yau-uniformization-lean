import Yau.Proofs.Y03RowProjection
import Yau.Proofs.Y03CoordinateInclusion

/-! The actual selected row span, with its coefficient representation and threshold nesting. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def rowLinearMap (B : Herm n) : ComplexVector n →L[ℂ] ComplexVector n :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B.transpose

theorem rowLinearMap_apply (B : Herm n) (v : ComplexVector n) : rowLinearMap B v = rowApply B v := by
  apply WithLp.ofLp_injective
  exact Matrix.mulVec_transpose B (WithLp.ofLp v)

def selectedRowSpace (B : Herm n) (s : Finset (Fin n)) : Submodule ℂ (ComplexVector n) :=
  LinearMap.range ((rowLinearMap B).toLinearMap.comp (coordinateSubspace s).subtype)

theorem selectedRowSpace_mono (B : Herm n) {s t : Finset (Fin n)} (hst : s ⊆ t) :
    selectedRowSpace B s ≤ selectedRowSpace B t := by
  rintro a ⟨c, hc⟩
  exact ⟨⟨c.1, coordinateSubspace_mono hst c.2⟩, hc⟩

theorem selectedRowSpace_projection_bound (μ ν : Fin n → ℝ) (U E : Herm n)
    (hU : Unitary U) {δ B g : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hB : 0 ≤ B) (hg : 0 < g) (hE : matOpNorm E ≤ δ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ B) (hν : ∀ i, 0 ≤ ν i ∧ ν i ≤ B)
    (horder : ∀ v : Fin n → ℂ, (∑ i, μ i * ‖(v ᵥ* U) i‖ ^ 2) ≤ ∑ i, ν i * ‖v i‖ ^ 2)
    (wold wnew : Fin n → ℝ)
    (hpassage : ∀ i l, μ l - g ≤ ν i → wold l ≤ wnew i)
    (hsmall : 32 * δ * B ≤ g / 2) (x : ℝ)
    (a : selectedRowSpace ((1 + E) * U) (Finset.univ.filter (fun i => wnew i ≤ x))) :
    ‖a‖ ≤ Real.sqrt (2 * (B + g) / g) *
      ‖coordinateProjectionOnto (Finset.univ.filter (fun i => wold i ≤ x)) a‖ := by
  let sold := Finset.univ.filter (fun i => wold i ≤ x)
  let snew := Finset.univ.filter (fun i => wnew i ≤ x)
  obtain ⟨c, hc⟩ := a.property
  have hca : rowApply ((1 + E) * U) (c : ComplexVector n) = (a : ComplexVector n) :=
    (rowLinearMap_apply _ _).symm.trans hc
  by_cases hne : snew.Nonempty
  · obtain ⟨imax, himax, hmax⟩ := Finset.exists_max_image snew ν hne
    have hout (l : Fin n) (hl : l ∉ sold) : ν imax + g ≤ μ l := by
      by_contra hn
      have hweight := hpassage imax l (by linarith)
      have hnew : wnew imax ≤ x := (Finset.mem_filter.1 himax).2
      exact hl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hweight.trans hnew⟩)
    have hcoef (i : Fin n) (hi : (c : ComplexVector n) i ≠ 0) : ν i ≤ ν imax := by
      apply hmax i
      by_contra hn
      exact hi (c.property i hn)
    have hp := perturbed_row_projection_mass μ ν U E hU hδ hδ' hB (hν imax).1 (hν imax).2 hg
      hE hμ horder sold hout hsmall (c : ComplexVector n) hcoef
    rw [hca] at hp
    exact norm_le_of_projection_mass (a : ComplexVector n) (coordinateProjection sold a) hg hB hp
  · have hempty : snew = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    have hc0 : (c : ComplexVector n) = 0 := by
      ext i
      exact c.property i (by change i ∉ snew; rw [hempty]; simp)
    have ha0 : (a : ComplexVector n) = 0 := by rw [← hca, hc0]; simp [rowApply]
    change ‖(a : ComplexVector n)‖ ≤ Real.sqrt (2 * (B + g) / g) *
      ‖coordinateProjection sold (a : ComplexVector n)‖
    simp only [ha0, norm_zero, map_zero, mul_zero, le_refl]

end Yau.Blueprint.Alignment.Y03Proof
