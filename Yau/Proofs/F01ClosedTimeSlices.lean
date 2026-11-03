import spec.CHAIN.CONTRACTS

/-! Joint closed-slab smoothness gives genuine spatial second jets and
one-sided time derivatives at both faces. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem contDiffOn_space_slice {F : ComplexVector n × ℝ → ℝ}
    {S : Set (ComplexVector n)} {I : Set ℝ} (hF : ContDiffOn ℝ ∞ F (S ×ˢ I))
    {t : ℝ} (ht : t ∈ I) : ContDiffOn ℝ ∞ (fun z => F (z, t)) S :=
  hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)

theorem contDiffOn_time_slice {F : ComplexVector n × ℝ → ℝ}
    {S : Set (ComplexVector n)} {I : Set ℝ} (hF : ContDiffOn ℝ ∞ F (S ×ˢ I))
    {z : ComplexVector n} (hz : z ∈ S) : ContDiffOn ℝ ∞ (fun t => F (z, t)) I :=
  hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨hz, ht⟩)

theorem closed_slab_slice_jets {F : ComplexVector n × ℝ → ℝ}
    {S : Set (ComplexVector n)} {I : Set ℝ} (hF : ContDiffOn ℝ ∞ F (S ×ˢ I))
    (hS : IsOpen S) {z : ComplexVector n} (hz : z ∈ S) {t : ℝ} (ht : t ∈ I) :
    ContDiffAt ℝ 2 (fun w => F (w, t)) z ∧
      DifferentiableWithinAt ℝ (fun s => F (z, s)) I t := by
  exact ⟨((contDiffOn_space_slice hF ht).contDiffAt (hS.mem_nhds hz)).of_le (by simp),
    (contDiffOn_time_slice hF hz t ht).differentiableWithinAt (by simp)⟩

end Yau.NodeProofs.F01Aux
