import spec.CHAIN.CONTRACTS

/-! The original jointly smooth metric-family condition supplies its actual
closed-time slices, and a fixed smooth field supplies a constant family. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamilySmooth_const {g : HermitianField M} (hg : MetricSmooth g) (I : Set ℝ) :
    MetricFamilySmooth (fun _ => g) I := by
  intro a b c
  exact (hg a b c).comp contDiffOn_fst (fun _ hp => hp.1)

theorem metricFamilySmooth_slice {h : ℝ → HermitianField M} {I : Set ℝ}
    (hh : MetricFamilySmooth h I) {t : ℝ} (ht : t ∈ I) : MetricSmooth (h t) := by
  intro a b c
  have hmap : ContDiffOn ℝ ∞ (fun z : ComplexVector n => (z, t)) (chartTarget a) :=
    contDiffOn_id.prodMk contDiffOn_const
  exact (hh a b c).comp hmap (fun _ hz => ⟨hz, ht⟩)

end Yau.NodeProofs.F01Aux
