import Yau.Proofs.P03LocalWeyl
import Yau.Proofs.P03WeylGlue

open scoped Topology ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- Local weak CR regularity for the actual measure and Wirtinger convention.
All dimensions and all open sets, including zero dimension and the empty
set, are covered by the same fixed-convolution and countable-gluing proof. -/
theorem localCRWeyl {n : ℕ} (U : Set (ComplexVector n)) (u : ComplexVector n → ℂ)
    (hU : IsOpen U) (hm : AEStronglyMeasurable u ((lebesgueC n).restrict U))
    (hL2 : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ U →
      MemLp u 2 ((lebesgueC n).restrict K))
    (hweak : ∀ (i : Fin n) (ψ : ComplexVector n → ℂ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ z, u z * wirtBar ψ z (stdVec i) ∂lebesgueC n) = 0) :
    ∃ v : ComplexVector n → ℂ,
      DifferentiableOn ℂ v U ∧ u =ᵐ[(lebesgueC n).restrict U] v := by
  classical
  rw [actualMeasure_eq_volume n] at hm hL2 hweak ⊢
  have hlocal (a : U) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall a.1 (4 * r) ⊆ U := by
    obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds a.2)
    refine ⟨R / 4, div_pos hR (by norm_num), ?_⟩
    have hrad : 4 * (R / 4) = R := by ring
    simpa only [hrad] using hRU
  choose r hr hKU using hlocal
  have hrep (a : U) : ∃ g : ComplexVector n → ℂ, ContDiff ℝ ∞ g ∧
      DifferentiableOn ℂ g (Metric.ball a.1 (3 * r a)) ∧
      u =ᵐ[(volume : Measure (ComplexVector n)).restrict (Metric.ball a.1 (2 * r a))] g :=
    local_holomorphic_representative (hr a) (hKU a)
      (hL2 _ (isCompact_closedBall _ _) (hKU a)) hweak
  choose g hg hgH hae using hrep
  exact glue_local_holomorphic_representatives r hr hKU g
    (fun a => (hg a).continuous) hgH hae

end Yau.NodeProofs.P03Aux
