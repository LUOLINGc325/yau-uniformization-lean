import Yau.Proofs.P04LeviCharts

noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem levi_inChart_posSemidef_of_overlap {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (hpos : (leviC (inChart b ψ) (chartPt b (chartInv a z))).PosSemidef) :
    (leviC (inChart a ψ) z).PosSemidef := by
  rw [levi_inChart_congruence hψ a b hz hy]
  exact hpos.conjTranspose_mul_mul_same _

theorem smooth_psh_all_charts {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (hpos : ∀ x, (levi ψ x).PosSemidef) :
    ∀ a z, z ∈ chartTarget a → (leviC (inChart a ψ) z).PosSemidef := by
  intro a z hz
  apply levi_inChart_posSemidef_of_overlap hψ a (chartInv a z) hz (mem_extChartAt_source _)
  exact hpos (chartInv a z)

end Yau.Proofs.P04Aux
