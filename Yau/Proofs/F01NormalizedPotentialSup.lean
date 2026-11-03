import Yau.Proofs.F01ParabolicDilation
import Yau.Proofs.F01MetricComparisonScalarBounds

/-! The genuine coarse metric sandwich bounds the actual scalar time
jet, and hence the normalized zero-extended potential on the unit cylinder.
No spatial or time derivative bound is inferred from smoothness. -/
noncomputable section
open Set Metric
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {M : ComplexManifold n}

theorem normalized_zero_potential_sup_of_time_cap
    {F D : Point n → ℝ} {ρ r T B : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T) (hB : 0 ≤ B)
    (hF0 : ∀ x ∈ ball 0 r, F (x, 0) = 0)
    (hJet : ∀ x ∈ ball 0 r, ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun t => F (x, t)) (D (x, s)) (Icc 0 T) s)
    (hD : ∀ x ∈ ball 0 r, ∀ s ∈ Icc 0 T, |D (x, s)| ≤ B) :
    ∀ p ∈ ball 0 1 ×ˢ Icc (-1) 1,
      |forwardZeroSpaceTime (parabolicRescalePotential ρ F) p| ≤ B := by
  intro p hp
  by_cases ht : p.2 ≤ 0
  · simpa only [forwardZeroSpaceTime, forwardZeroExtension, ht, ite_true, abs_zero] using hB
  · have hp0 : p.2 ∈ Icc (0 : ℝ) 1 := ⟨(lt_of_not_ge ht).le, hp.2.2⟩
    have hxρ : ρ • p.1 ∈ ball (0 : Space n) r := spatialDilation_mem_ball hρ hρr hp.1
    have hv0 : parabolicRescalePotential ρ F (p.1, 0) = 0 := by
      change (ρ ^ 2)⁻¹ * F (ρ • p.1, ρ ^ 2 * 0) = 0
      rw [mul_zero, hF0 _ hxρ, mul_zero]
    have hcurve : ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun t => parabolicRescalePotential ρ F (p.1, t))
          (D (parabolicDilation ρ (p.1, s))) (Icc 0 1) s := by
      intro s hs
      exact parabolicRescalePotential_time_jet hρ hρr hρT hJet
        (p := (p.1, s)) ⟨hp.1, hs⟩
    have hcap : ∀ s ∈ Icc (0 : ℝ) 1, |D (parabolicDilation ρ (p.1, s))| ≤ B := by
      intro s hs
      have hm : parabolicDilation ρ (p.1, s) ∈ ball 0 r ×ˢ Icc 0 T :=
        parabolicDilation_maps_positive hρ hρr hρT (x := (p.1, s)) ⟨hp.1, hs⟩
      exact hD _ hm.1 _ hm.2
    have hb := closed_potential_abs_bound_of_time_value
      (U := fun t => parabolicRescalePotential ρ F (p.1, t))
      (P := fun t => D (parabolicDilation ρ (p.1, t))) zero_le_one hv0 hcurve hcap p.2 hp0
    change |if p.2 ≤ 0 then 0 else parabolicRescalePotential ρ F p| ≤ B
    rw [ite_eq_right_iff.mpr (fun h => (ht h).elim)]
    exact hb.trans (mul_le_of_le_one_right hB hp.2.2)

theorem normalized_potential_sup_of_metric_sandwich
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {ρ r T C : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hC : 1 ≤ C) (hU0 : ∀ x, U x 0 = 0)
    (hJet : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
      ((C : ℂ) • gMat α x - gMat (h s) x).PosSemidef)
    (e : Space n → M.Carrier) :
    ∀ p ∈ ball 0 1 ×ˢ Icc (-1) 1,
      |forwardZeroSpaceTime (parabolicRescalePotential ρ (fun q : Point n => U (e q.1) q.2)) p| ≤
        (n : ℝ) * Real.log C := by
  apply normalized_zero_potential_sup_of_time_cap
    (F := fun q : Point n => U (e q.1) q.2)
    (D := fun q : Point n => flowLogDetRatio α h (e q.1) q.2) hρ hρr hρT
    (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hC))
    (fun x _ => hU0 (e x)) (fun x _ s hs => hJet (e x) s hs)
  intro x hx s hs
  exact logdet_ratio_abs_bound_of_sandwich
    (Yau.LeafProofs.L12Aux.hMat_posDef α (e x) (chartPt (e x) (e x)) (mem_extChartAt_target (e x)))
    (Yau.LeafProofs.L12Aux.hMat_posDef (h s) (e x) (chartPt (e x) (e x)) (mem_extChartAt_target (e x))) hC
    (hflow (e x) s hs).1 (hflow (e x) s hs).2

end Yau.NodeProofs.F01Aux
