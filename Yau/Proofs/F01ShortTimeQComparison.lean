import Yau.Proofs.F01MetricComparisonScalarBounds
import Yau.Proofs.F01ComparisonMaximum
import Yau.Proofs.F01ComparisonHeatIdentity
import Yau.Proofs.F01ClosedScalarHeat
import Yau.Proofs.F01LogDetRatioSmooth
import Yau.Proofs.F01ComparisonTraceBound

/-! The original short-time potential tuple, its original finite metric
sandwich, and an actual nonpositive smooth weight construct the same explicit Q
with its nonnegativity and positive native heat inequality at both faces. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem short_time_comparison_Q
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T C D c B : ℝ}
    (hT : 0 < T) (hC1 : 1 ≤ C) (hD : 0 ≤ D) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hh0 : h 0 = α) (hU0 : ∀ x, U x 0 = 0)
    (hlo : ∀ x t, t ∈ Icc 0 T → (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef)
    (hhi : ∀ x t, t ∈ Icc 0 T → ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (hφsign : ∀ x, φ x ≤ 0)
    (hweight : ∀ x, (gMat α x - (D : ℂ) • ricci α x +
      (D : ℂ) • levi φ x - (c : ℂ) • gMat α x).PosSemidef)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hf0 : ∀ x, 0 ≤ f x)
    (hproper : ∀ b : ℝ, IsCompact {x | f x ≤ b})
    (hfLevi : ∀ x, ((B : ℂ) • gMat α x - levi f x).PosSemidef) :
    SmoothSpaceTime (comparisonFunction D n U (flowLogDetRatio α h) φ) (Icc 0 T) ∧
      ∀ x t, t ∈ Icc 0 T →
        0 ≤ comparisonFunction D n U (flowLogDetRatio α h) φ x t ∧
        c * traceWith (gMat (h t) x) (gMat α x) ≤
          fieldHeatWithin h (Icc 0 T)
            (fun s y => comparisonFunction D n U (flowLogDetRatio α h) φ y s) x t := by
  let CP := (n : ℝ) * Real.log C
  have hCP : 0 ≤ CP := mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hC1)
  have hP := flowLogDetRatio_smoothSpaceTime α hα h hh
  have hP0 := flowLogDetRatio_initial α h hh0
  have hPbound (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) : |flowLogDetRatio α h x t| ≤ CP :=
    logdet_ratio_abs_bound_of_sandwich
      (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x))
      (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
      hC1 (hlo x t ht) (hhi x t ht)
  have hUbound (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) : |U x t| ≤ CP * T :=
    (closed_potential_abs_bound_of_time_value hT.le (hU0 x) (hpde x) (hPbound x) t ht).trans
      (mul_le_mul_of_nonneg_left ht.2 hCP)
  have hlap (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      laplacian (h t) f x ≤ B * (C * n) :=
    laplacian_bound_from_metric_comparison α (h t) f x (zero_lt_one.trans_le hC1)
      hB (hlo x t ht) (hfLevi x)
  have hheat (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :=
    comparisonFunction_heat_lower α h U (flowLogDetRatio α h) φ D x ((uniqueDiffOn_Icc hT) t ht)
      (closed_slab_logdet_evolution_and_heat α hα h U hT hh hU hpot hpde x ht).1
      (hpde x t ht) (smoothSpaceTime_slice hU ht) (smoothSpaceTime_slice hP ht) hφ (hpot t ht)
      (closed_slab_logdet_evolution_and_heat α hα h U hT hh hU hpot hpde x ht).2 (hweight x)
  have hnonneg := comparisonFunction_nonneg h hT hD hCP hU hP hφ hφsign hU0 hP0
    hUbound hPbound f hf hf0 hproper hlap (fun x t ht => by
      have htrace := traceWith_posSemidef_nonneg
        (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
        (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)).posSemidef
      exact (mul_nonneg hc htrace).trans (hheat x t ⟨ht.1.le, ht.2⟩))
  exact ⟨comparisonFunction_smoothSpaceTime hU hP hφ D,
    fun x t ht => ⟨hnonneg x t ht, hheat x t ht⟩⟩

end Yau.NodeProofs.F01Aux
