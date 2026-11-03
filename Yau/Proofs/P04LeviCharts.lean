import Yau.Proofs.P04ChartDerivativeInverse

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual Levi congruence between arbitrary original overlapping charts. -/
theorem levi_inChart_congruence {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    leviC (inChart a ψ) z =
      (L17Aux.linearMatrix (fderiv ℂ (fun w => chartPt b (chartInv a w)) z))ᴴ*
        leviC (inChart b ψ) (chartPt b (chartInv a z))*
      L17Aux.linearMatrix (fderiv ℂ (fun w => chartPt b (chartInv a w)) z) := by
  have hT := L18Aux.chartTransition_contDiffAt a b hz hy
  have htarget : chartPt b (chartInv a z) ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source hy
  have hf : ContDiffAt ℝ 2 (inChart b ψ) (chartPt b (chartInv a z)) :=
    ((hψ b).contDiffAt ((isOpen_extChartAt_target b).mem_nhds htarget)).of_le (by simp)
  have heq : inChart a ψ =ᶠ[𝓝 z]
      (inChart b ψ ∘ fun w => chartPt b (chartInv a w)) := by
    filter_upwards [(canonicalOverlap_isOpen b a).mem_nhds ⟨hz,hy⟩] with w hw
    change ψ (chartInv a w)=ψ (chartInv b (chartPt b (chartInv a w)))
    rw [show chartInv b (chartPt b (chartInv a w))=chartInv a w from
      (extChartAt (ComplexModel n) b).left_inv hw.2]
  rw [L22Aux.leviC_congr_of_eventuallyEq heq]
  exact L17Aux.leviC_comp (hT.of_le (by simp)) hf

theorem levi_inChart_posDef_of_overlap {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (hpos : (leviC (inChart b ψ) (chartPt b (chartInv a z))).PosDef) :
    (leviC (inChart a ψ) z).PosDef := by
  rw [levi_inChart_congruence hψ a b hz hy]
  exact hpos.conjTranspose_mul_mul_same
    (linearMatrix_mulVec_injective _ (chartTransition_fderiv_injective a b hz hy))

/-- The centered strictness in the ORIGINAL definition implies actual
strict positivity everywhere in every original chart. -/
theorem smooth_strictPsh_all_charts {ψ : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ) :
    ∀ a z, z ∈ chartTarget a → (leviC (inChart a ψ) z).PosDef := by
  intro a z hz
  apply levi_inChart_posDef_of_overlap hψ.1 a (chartInv a z) hz (mem_extChartAt_source _)
  exact hψ.2 (chartInv a z)

end Yau.Proofs.P04Aux
