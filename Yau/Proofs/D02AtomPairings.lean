import Yau.Proofs.D02AtomCutoffs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Smooth local density pairings force the actual positive measure to
have no point mass. The cutoff sequence and both dominated convergence
arguments are constructed on one finite interior compact set. -/

open scoped Topology ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem atom_zero_of_smooth_test_pairings {U : Set ℂ} (hU : IsOpen U)
    (μ : Measure ℂ) (a : ℂ → ℝ) (ha : ContinuousOn a U)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hp : ∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      (2 * Real.pi) * (∫ z, χ z ∂μ) = ∫ z, a z * χ z)
    {z₀ : ℂ} (hz : z₀ ∈ U) : μ {z₀} = 0 := by
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  let K := closedBall z₀ R
  let ν := μ.restrict K
  letI : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using hμ K (isCompact_closedBall _ _) hRU⟩
  obtain ⟨χ, hχ, hχrange, hχone, hχlim⟩ := exists_atom_cutoffs z₀ hR
  have hχK (j : ℕ) : tsupport (χ j) ⊆ K := (hχ j).2.2.trans ball_subset_closedBall
  have hχU (j : ℕ) : tsupport (χ j) ⊆ U := (hχK j).trans hRU
  let b : ℂ → ℝ := ({z₀} : Set ℂ).indicator (fun _ => 1)
  have hleft : Tendsto (fun j => ∫ z, χ j z ∂ν) atTop (𝓝 ((μ {z₀}).toReal)) := by
    have ht := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : ℂ => (1 : ℝ))
      (fun j => (hχ j).1.continuous.aestronglyMeasurable) (integrable_const 1)
      (fun j => Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hχrange j z).1] using (hχrange j z).2)
      (Eventually.of_forall hχlim)
    have hi : (∫ z, b z ∂ν) = (μ {z₀}).toReal := by
      have hs : ({z₀} : Set ℂ) ⊆ K := singleton_subset_iff.mpr (mem_closedBall_self hR.le)
      rw [integral_indicator_const 1 (measurableSet_singleton z₀)]
      simp only [smul_eq_mul, mul_one, Measure.real, ν,
        Measure.restrict_apply (measurableSet_singleton z₀),
        inter_eq_left.mpr hs]
    simpa only [← hi, b] using ht
  have hai : IntegrableOn a K volume := (ha.mono hRU).integrableOn_compact (isCompact_closedBall _ _)
  have hright : Tendsto (fun j => ∫ z in K, a z * χ j z) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict K) (fun z => ‖a z‖)
      (fun j => hai.aestronglyMeasurable.mul (hχ j).1.continuous.aestronglyMeasurable)
      hai.norm (fun j => Eventually.of_forall fun z => by
        change ‖a z * χ j z‖ ≤ ‖a z‖
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left
          (show ‖χ j z‖ ≤ 1 from by
            simpa only [Real.norm_eq_abs, abs_of_nonneg (hχrange j z).1] using (hχrange j z).2)
          (norm_nonneg _)).trans_eq (mul_one _))
      (Eventually.of_forall fun z => (hχlim z).const_mul (a z))
    have hbzero : (fun z => a z * b z) =ᵐ[volume.restrict K] (fun _ => (0 : ℝ)) := by
      have hne : ∀ᵐ z : ℂ ∂volume, z ≠ z₀ := by simp [ae_iff]
      filter_upwards [ae_restrict_of_ae hne] with z hz
      have hznot : z ∉ ({z₀} : Set ℂ) := by simpa only [mem_singleton_iff] using hz
      simp only [b, indicator_of_notMem hznot, mul_zero]
    have hi : (∫ z in K, a z * b z) = 0 := by
      rw [integral_congr_ae hbzero, integral_zero]
    simpa only [← hi, b, Pi.mul_apply] using ht
  have hpair (j : ℕ) : (2 * Real.pi) * (∫ z, χ j z ∂ν) = ∫ z in K, a z * χ j z := by
    have hleftEq : (∫ z in K, χ j z ∂μ) = ∫ z, χ j z ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
        image_eq_zero_of_notMem_tsupport (fun h => hz (hχK j h)))
    have hrightEq : (∫ z in K, a z * χ j z) = ∫ z, a z * χ j z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hχK j h)), mul_zero])
    rw [hrightEq]
    change (2 * Real.pi) * (∫ z in K, χ j z ∂μ) = _
    rw [hleftEq]
    exact hp (χ j) (hχ j).1 (hχ j).2.1 (hχU j)
  have heq : (2 * Real.pi) * (μ {z₀}).toReal = 0 :=
    tendsto_nhds_unique (hleft.const_mul (2 * Real.pi)) (hright.congr' (Eventually.of_forall fun j => (hpair j).symm))
  have hreal : (μ {z₀}).toReal = 0 := (mul_eq_zero.mp heq).resolve_left (by positivity)
  have hfinite : μ {z₀} < ⊤ := (measure_mono (singleton_subset_iff.mpr (mem_closedBall_self hR.le))).trans_lt
    (hμ K (isCompact_closedBall _ _) hRU)
  exact (ENNReal.toReal_eq_zero_iff (μ {z₀})).mp hreal |>.resolve_right hfinite.ne

end Yau.NodeProofs.D02Aux
