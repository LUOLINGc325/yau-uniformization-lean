import Yau.LeafProofs.L17AtlasCutoffs

/-! The actual locally finite sum normalization of the uniform chart weights. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

def chartWeightSum {g : HermitianField M} (A : BoundedChartFamily g)
    (S : Set M.Carrier) (ρ : ℝ) (hρ : 0 < ρ) (x : M.Carrier) : ℝ :=
  ∑ᶠ p : S, chartWeight (A.chart p) ρ hρ x

def normalizedChartWeight {g : HermitianField M} (A : BoundedChartFamily g)
    (S : Set M.Carrier) (ρ : ℝ) (hρ : 0 < ρ) (p : S) (x : M.Carrier) : ℝ :=
  chartWeight (A.chart p) ρ hρ x / chartWeightSum A S ρ hρ x

theorem BoundedChartFamily.chartWeights_locallyFinite
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hLoc : LocallyFinite (fun p : S => A.chart p '' closedBall 0 ρ)) :
    LocallyFinite (fun p : S => Function.support (chartWeight (A.chart p) ρ hρ)) := by
  apply hLoc.subset
  intro p
  apply subset_trans (subset_closure : Function.support (chartWeight (A.chart p) ρ hρ) ⊆
    tsupport (chartWeight (A.chart p) ρ hρ))
  apply (A.chartWeight_properties p hρ hρr).2.2.trans
  apply image_mono
  intro z hz
  exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (by linarith))

theorem BoundedChartFamily.chartWeightSum_smooth
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hLoc : LocallyFinite (fun p : S => A.chart p '' closedBall 0 ρ)) :
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (chartWeightSum A S ρ hρ) := by
  let := L12Aux.manifold_realSmooth M
  apply contMDiff_finsum
  · intro p
    exact L18Aux.contMDiff_real_of_smoothFn (A.chartWeight_properties p hρ hρr).2.1
  · exact A.chartWeights_locallyFinite S hρ hρr hLoc

theorem BoundedChartFamily.one_le_chartWeightSum
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hcover : ∀ x : M.Carrier, ∃ p ∈ S, x ∈ A.chart p '' ball 0 (ρ / 4))
    (hLoc : LocallyFinite (fun p : S => A.chart p '' closedBall 0 ρ)) (x : M.Carrier) :
    1 ≤ chartWeightSum A S ρ hρ x := by
  obtain ⟨p, hp, hx⟩ := hcover x
  have hfin := (A.chartWeights_locallyFinite S hρ hρr hLoc).point_finite x
  have hle := single_le_finsum (⟨p, hp⟩ : S) hfin
    (fun q : S => (chartWeight_mem_Icc (A.chart q) hρ x).1)
  have hone := A.chartWeight_one p hρ hρr (image_mono ball_subset_closedBall hx)
  simpa only [hone, chartWeightSum] using hle

theorem BoundedChartFamily.normalizedChartWeight_smooth
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hcover : ∀ x : M.Carrier, ∃ p ∈ S, x ∈ A.chart p '' ball 0 (ρ / 4))
    (hLoc : LocallyFinite (fun p : S => A.chart p '' closedBall 0 ρ)) (p : S) :
    SmoothFn (normalizedChartWeight A S ρ hρ p) := by
  let := L12Aux.manifold_realSmooth M
  apply L18Aux.smoothFn_of_contMDiff_real
  exact (L18Aux.contMDiff_real_of_smoothFn (A.chartWeight_properties p hρ hρr).2.1).div₀
    (A.chartWeightSum_smooth S hρ hρr hLoc)
    (fun x => (lt_of_lt_of_le zero_lt_one (A.one_le_chartWeightSum S hρ hρr hcover hLoc x)).ne')

theorem normalizedChartWeight_tsupport_subset
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (p : S) :
    tsupport (normalizedChartWeight A S ρ hρ p) ⊆
      tsupport (chartWeight (A.chart p) ρ hρ) := by
  apply closure_mono
  intro x hx
  change chartWeight (A.chart p) ρ hρ x ≠ 0
  intro hzero
  exact hx (by simp only [normalizedChartWeight, hzero, zero_div])

theorem BoundedChartFamily.normalizedChartWeight_nonneg
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (p : S) (x : M.Carrier) :
    0 ≤ normalizedChartWeight A S ρ hρ p x := by
  apply div_nonneg (chartWeight_mem_Icc (A.chart p) hρ x).1
  exact finsum_nonneg fun q : S => (chartWeight_mem_Icc (A.chart q) hρ x).1

theorem BoundedChartFamily.normalizedChartWeight_sum
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hcover : ∀ x : M.Carrier, ∃ p ∈ S, x ∈ A.chart p '' ball 0 (ρ / 4))
    (hLoc : LocallyFinite (fun p : S => A.chart p '' closedBall 0 ρ)) (x : M.Carrier) :
    (∑ᶠ p : S, normalizedChartWeight A S ρ hρ p x) = 1 := by
  have hne : chartWeightSum A S ρ hρ x ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (A.one_le_chartWeightSum S hρ hρr hcover hLoc x)).ne'
  calc
    _ = (chartWeightSum A S ρ hρ x) * (chartWeightSum A S ρ hρ x)⁻¹ := by
      simpa only [normalizedChartWeight, div_eq_mul_inv, smul_eq_mul, chartWeightSum] using
        (finsum_smul (fun p : S => chartWeight (A.chart p) ρ hρ x)
          ((chartWeightSum A S ρ hρ x)⁻¹)).symm
    _ = 1 := mul_inv_cancel₀ hne

theorem BoundedChartFamily.chartLocalization_mul_normalizedWeight
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius) (p : S) (x : M.Carrier) :
    chartLocalization (A.chart p) ρ hρ x * normalizedChartWeight A S ρ hρ p x =
      normalizedChartWeight A S ρ hρ p x := by
  unfold normalizedChartWeight
  rw [← mul_div_assoc, A.chartLocalization_mul_weight p hρ hρr]

theorem BoundedChartFamily.normalizedChartWeight_le_one
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hcover : ∀ x : M.Carrier, ∃ p ∈ S, x ∈ A.chart p '' ball 0 (ρ / 4))
    (hLoc : LocallyFinite (fun p : S => A.chart p '' closedBall 0 ρ)) (p : S) (x : M.Carrier) :
    normalizedChartWeight A S ρ hρ p x ≤ 1 := by
  have hpos : 0 < chartWeightSum A S ρ hρ x :=
    lt_of_lt_of_le zero_lt_one (A.one_le_chartWeightSum S hρ hρr hcover hLoc x)
  apply (div_le_one hpos).mpr
  exact single_le_finsum p (A.chartWeights_locallyFinite S hρ hρr hLoc |>.point_finite x)
    (fun q : S => (chartWeight_mem_Icc (A.chart q) hρ x).1)

theorem BoundedChartFamily.normalizedChartWeight_hasCompactSupport
    {g : HermitianField M} (A : BoundedChartFamily g) (S : Set M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius) (p : S) :
    HasCompactSupport (normalizedChartWeight A S ρ hρ p) :=
  (A.chartWeight_properties p hρ hρr).1.of_isClosed_subset
    (isClosed_tsupport _) (normalizedChartWeight_tsupport_subset A S hρ p)

end Yau.LeafProofs.L17Aux
