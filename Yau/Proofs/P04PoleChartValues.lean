import Yau.Proofs.P04PoleWeights

noncomputable section
open Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem globalPolePart_inChart (p : M.Carrier) (χ : ComplexVector n → ℝ) (c ε : ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget p) :
    inChart p (globalPolePart p χ c ε) z=regularizedPoleModel χ (chartPt p p) c ε z := by
  have hy : chartInv p z ∈ (extChartAt (ComplexModel n) p).source :=
    (extChartAt (ComplexModel n) p).map_target hz
  change L18Aux.chartPushforwardZero p (regularizedPoleModel χ (chartPt p p) c ε) (chartInv p z)=_
  rw [L18Aux.chartPushforwardZero,if_pos hy]
  rw [show chartPt p (chartInv p z)=z from (extChartAt (ComplexModel n) p).right_inv hz]

theorem regularizedPoleWeight_inChart (p : M.Carrier) (χ : ComplexVector n → ℝ)
    (c k : ℝ) (ψ : M.Carrier → ℝ) (ε : ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget p) :
    inChart p (regularizedPoleWeight p χ c k ψ ε) z =
      k*inChart p ψ z+regularizedPoleModel χ (chartPt p p) c ε z := by
  change k*inChart p ψ z+inChart p (globalPolePart p χ c ε) z=_
  rw [globalPolePart_inChart p χ c ε hz]

/-- The regularized density is the genuine negative power away from its
strictly positive regularized argument, never a logarithm evaluated at zero. -/
theorem regularizedPoleModel_exp_factor (χ : ComplexVector n → ℝ) (z₀ : ComplexVector n)
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) (Φ : ComplexVector n → ℝ) (z : ComplexVector n) :
    Real.exp (-(Φ z+regularizedPoleModel χ z₀ c ε z)) =
      Real.exp (-Φ z)*(‖z-z₀‖^2+ε^2)^(-c*χ z) := by
  have hq : 0 < ‖z-z₀‖^2+ε^2 := by positivity
  rw [Real.rpow_def_of_pos hq,← Real.exp_add]
  congr 1
  unfold regularizedPoleModel
  ring

end Yau.Proofs.P04Aux
