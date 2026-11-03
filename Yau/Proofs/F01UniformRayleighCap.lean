import Yau.Proofs.F01ComparisonSupBound
import Yau.Proofs.F01RayleighSupAbsorption

/-! The actual Q bound and actual Rayleigh order absorb the finite
preliminary logarithmic supremum. The resulting metric constant does not
contain that preliminary comparison constant. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem uniform_rayleigh_cap_from_comparison
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (φ : M.Carrier → ℝ) (o : M.Carrier) {T D a Cpre Mφ : ℝ}
    (hT : 0 ≤ T) (hTD : T ≤ D) (ha : 0 ≤ a) (hMφ : 0 ≤ Mφ)
    (hsmall : 2 * a * (n : ℝ) * D < 1)
    (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio α h x s) (Icc 0 T) s)
    (hCpre : 0 < Cpre)
    (hpre : ∀ x t, t ∈ Icc 0 T → ((Cpre : ℂ) • gMat α x - gMat (h t) x).PosSemidef)
    (hφ : ∀ x, -Mφ ≤ φ x)
    (hQ : ∀ x t, t ∈ Icc 0 T → 0 ≤ comparisonFunction D n U (flowLogDetRatio α h) φ x t)
    (hRayleigh : ∀ x t, t ∈ Icc 0 T →
      ((Real.exp (rayleighPenalty a (comparisonFunction D n U (flowLogDetRatio α h) φ x t)) : ℂ) •
        gMat α x - gMat (h t) x).PosSemidef) :
    ∀ x t, t ∈ Icc 0 T →
      ((Real.exp ((2 * a * (D * Mφ + (n : ℝ) * T)) /
          (1 - 2 * a * (n : ℝ) * D)) : ℂ) • gMat α x - gMat (h t) x).PosSemidef := by
  let A := M.Carrier × {t : ℝ // t ∈ Icc 0 T}
  letI : Nonempty A := ⟨(o, ⟨0, le_rfl, hT⟩)⟩
  let F : A → ℝ := fun p => Real.log (metricLargestRayleigh α (h p.2.1) p.1)
  have hα (x : M.Carrier) : (gMat α x).PosDef :=
    Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hk (x : M.Carrier) (t : ℝ) : (gMat (h t) x).PosDef :=
    Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)
  have hbounded : BddAbove (range F) := by
    refine ⟨Real.log Cpre, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact Real.log_le_log (metricLargestRayleigh_pos α (h p.2.1) p.1)
      (largestMatrixRayleigh_le_of_order (hα p.1) hCpre.le (hpre p.1 p.2.1 p.2.2))
  let B := max 0 (sSup (range F))
  have hlog (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      Real.log (metricLargestRayleigh α (h t) x) ≤ B :=
    (le_csSup hbounded (mem_range_self (⟨x, ⟨t, ht⟩⟩ : A))).trans (le_max_right _ _)
  have hD : 0 ≤ D := hT.trans hTD
  have hq : 0 ≤ 2 * a * (n : ℝ) * D := by positivity
  have hr : 0 ≤ 2 * a * (D * Mφ + (n : ℝ) * T) := by positivity
  have hlinear (p : A) : F p ≤
      (2 * a * (n : ℝ) * D) * B + 2 * a * (D * Mφ + (n : ℝ) * T) := by
    have hEigen := largestMatrixRayleigh_le_of_order (hα p.1)
      (Real.exp_pos (rayleighPenalty a
        (comparisonFunction D n U (flowLogDetRatio α h) φ p.1 p.2.1))).le
      (hRayleigh p.1 p.2.1 p.2.2)
    have hLog := Real.log_le_log (metricLargestRayleigh_pos α (h p.2.1) p.1) hEigen
    rw [Real.log_exp] at hLog
    have hPenalty := rayleighPenalty_le_two_mul ha (hQ p.1 p.2.1 p.2.2)
    have hQcap := comparisonFunction_bound_of_log_largest α h U φ hT hTD hU0 hpde hlog hφ p.1 p.2.2
    have hmul := mul_le_mul_of_nonneg_left hQcap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
    change Real.log (metricLargestRayleigh α (h p.2.1) p.1) ≤ _
    nlinarith
  have hcap := bounded_range_linear_absorption F hbounded hq hsmall hr hlinear
  intro x t ht
  have hh := Real.exp_le_exp.mpr (hcap (⟨x, ⟨t, ht⟩⟩ : A))
  change Real.exp (Real.log (metricLargestRayleigh α (h t) x)) ≤ _ at hh
  rw [Real.exp_log (metricLargestRayleigh_pos α (h t) x)] at hh
  exact order_of_largestMatrixRayleigh_le (hα x) (hk x t) hh

end Yau.NodeProofs.F01Aux
