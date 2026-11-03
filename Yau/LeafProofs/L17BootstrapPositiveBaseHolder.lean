import Yau.LeafProofs.L17BootstrapPositiveBaseHolderAffine
import Yau.LeafProofs.L17BootstrapInverseHolder

/-! The actual small base metric has a uniform lower bound and an actual Hölder inverse. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

namespace Yau.LeafProofs.L17BootstrapPositiveBaseHolderAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux

local instance positiveBaseInverseMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) {T gamma : ℝ}

def baseLambda : ℝ := (P.charts.bound 0)⁻¹/2

theorem baseLambda_pos : 0 < baseLambda P :=
  div_pos (inv_pos.mpr (P.charts.bound_pos 0)) (by norm_num)

section PositiveBase
variable (hT : 0 < T) (hTime : T ≤ P.radius^2) (hgamma0 : 0 ≤ gamma)
  (hgamma1 : gamma ≤ 1) (hr : P.radius ≤ 1)
variable (u : SchauderSpace P T gamma hT)
variable (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts ≤ (P.charts.bound 0)⁻¹)
include hSmall

theorem Hstar_posDef (q : LocalCylinder P T) :
    (Hstar P hT hTime hgamma0 hgamma1 hr u q).PosDef := by
  rw [Hstar_value]
  exact (coordinateMetric_half_double u hSmall q).1

theorem Hstar_uniform_lower (q : LocalCylinder P T) :
    (Hstar P hT hTime hgamma0 hgamma1 hr u q -
      (baseLambda P : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  let G := pullbackMatrix g (P.charts.chart q.1) q.2.1
  let a := (P.charts.bound 0)⁻¹
  have hHalf : (Hstar P hT hTime hgamma0 hgamma1 hr u q-(1/2:ℂ) • G).PosSemidef := by
    simpa only [Hstar_value] using (coordinateMetric_half_double u hSmall q).2.1
  have hBG : (G-(a:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    simpa only [G,a,Complex.ofReal_inv] using
      (P.charts.comparison q.1 q.2.1 ((ball_subset_ball P.radius_lt.le) q.2.1.property)).1
  have hSum := hHalf.add (hBG.smul (by norm_num [Complex.le_def] : (0:ℂ) ≤ 1/2))
  have hId :
      (Hstar P hT hTime hgamma0 hgamma1 hr u q-(1/2:ℂ) • G) +
        (1/2:ℂ) • (G-(a:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      Hstar P hT hTime hgamma0 hgamma1 hr u q -
        (baseLambda P : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      baseLambda,Complex.ofReal_div,Complex.ofReal_ofNat]
    dsimp only [a]
    ring
  rw [hId] at hSum
  exact hSum

/-- This inverse is obtained from the actual positive base metric and the proved B1 construction. -/
theorem exists_Hstar_inverse :
    ∃ (K : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) (B : ℝ),
      1 ≤ B ∧
      (∀ q : LocalCylinder P T, K q=(Hstar P hT hTime hgamma0 hgamma1 hr u q)⁻¹) ∧
      Hstar P hT hTime hgamma0 hgamma1 hr u*K=1 ∧
      K*Hstar P hT hTime hgamma0 hgamma1 hr u=1 ∧
      ‖K‖ ≤ 2*(1+B+B^2*‖(Hstar P hT hTime hgamma0 hgamma1 hr u).value‖) :=
  L17BootstrapInverseHolderAux.exists_inverse_holder_of_uniform_positive
    (Hstar P hT hTime hgamma0 hgamma1 hr u) (baseLambda P) (baseLambda_pos P)
    (Hstar_uniform_lower P hT hTime hgamma0 hgamma1 hr u hSmall)

end PositiveBase
end Yau.LeafProofs.L17BootstrapPositiveBaseHolderAux
