import Yau.Proofs.F01RayleighCapScale

/-! The same actual flow and potential have a metric upper bound uniform
over every smaller comparison interval. The preliminary sandwich constant
does not enter the result. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem fixed_time_rayleigh_cap_from_comparison
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (φ : M.Carrier → ℝ) (o : M.Carrier) {T D L Cpre Mφ : ℝ}
    (hT : 0 ≤ T) (hTD : T ≤ D) (hL : 0 < L) (hMφ : 0 ≤ Mφ)
    (hscale : 4 * (n : ℝ) * D ≤ L)
    (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio α h x s) (Icc 0 T) s)
    (hCpre : 0 < Cpre)
    (hpre : ∀ x t, t ∈ Icc 0 T → ((Cpre : ℂ) • gMat α x - gMat (h t) x).PosSemidef)
    (hφ : ∀ x, -Mφ ≤ φ x)
    (hQ : ∀ x t, t ∈ Icc 0 T → 0 ≤ comparisonFunction D n U (flowLogDetRatio α h) φ x t)
    (hRayleigh : ∀ x t, t ∈ Icc 0 T →
      ((Real.exp (rayleighPenalty L⁻¹ (comparisonFunction D n U (flowLogDetRatio α h) φ x t)) : ℂ) •
        gMat α x - gMat (h t) x).PosSemidef) :
    ∀ x t, t ∈ Icc 0 T →
      ((Real.exp (4 * D * (Mφ + n) / L) : ℂ) • gMat α x - gMat (h t) x).PosSemidef := by
  have hcap := uniform_rayleigh_cap_from_comparison α h U φ o hT hTD
    (inv_nonneg.mpr hL.le) hMφ (absorbed_rayleigh_coefficient_lt_one hL hscale)
    hU0 hpde hCpre hpre hφ hQ hRayleigh
  intro x t ht
  have hα := Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hh := Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)
  have heig := largestMatrixRayleigh_le_of_order hα
    (Real.exp_pos ((2 * L⁻¹ * (D * Mφ + (n : ℝ) * T)) /
      (1 - 2 * L⁻¹ * (n : ℝ) * D))).le (hcap x t ht)
  exact order_of_largestMatrixRayleigh_le hα hh (heig.trans
    (Real.exp_le_exp.mpr (absorbed_rayleigh_exponent_le hL hT hTD hMφ hscale)))

end Yau.NodeProofs.F01Aux
