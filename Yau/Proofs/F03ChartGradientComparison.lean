import Yau.Proofs.F03GradientPairNorm

/-! Compact positivity of the actual real metric converts physical gradient bounds to genuine chart differential bounds. -/
noncomputable section
open Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def chartRealCovectorEnergy (g : HermitianField M) (a : M.Carrier)
    (z : ComplexVector n) (D : ComplexVector n →L[ℝ] ℝ) : ℝ :=
  ∑ i,∑ j,(realMetricFn g a z)⁻¹ i j*D (realVec i)*D (realVec j)

theorem chartRealCovectorEnergy_pos (g : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a)
    {D : ComplexVector n →L[ℝ] ℝ} (hD : D ≠ 0) :
    0 < chartRealCovectorEnergy g a z D := by
  have hCoord : (fun i : RIdx n => D (realVec i)) ≠ 0 := by
    intro hZero
    apply hD
    ext v
    rw [← sum_realCoord_realVec v,map_sum]
    simp only [map_smul,smul_eq_mul]
    have hi (i : RIdx n) : D (realVec i)=0 := congrFun hZero i
    simp only [hi,mul_zero,Finset.sum_const_zero,ContinuousLinearMap.zero_apply]
  have hPos := (realMetricFn_posDef g a z hz).inv.dotProduct_mulVec_pos hCoord
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,star_trivial] at hPos
  unfold chartRealCovectorEnergy
  convert hPos using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem chartRealCovectorEnergy_smul (g : HermitianField M) (a : M.Carrier)
    (z : ComplexVector n) (c : ℝ) (D : ComplexVector n →L[ℝ] ℝ) :
    chartRealCovectorEnergy g a z (c • D)=c^2*chartRealCovectorEnergy g a z D := by
  simp only [chartRealCovectorEnergy,ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem chartRealCovectorEnergy_fderiv (g : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    chartRealCovectorEnergy g a z (fderiv ℝ (inChart a f) z)=
      2*gradNormSq g f (chartInv a z) := by
  rw [← scalarGradientPair_eq_twice_gradNormSq g hf,scalarGradientPair_eq_chart g hf hf a hz,
    chartGradientPair_eq_sum]
  rfl

theorem compact_chart_real_covector_coercivity (g : SmoothMetric M) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hKt : K ⊆ chartTarget a) :
    ∃ C : ℝ,0 < C ∧ ∀ z ∈ K,∀ D : ComplexVector n →L[ℝ] ℝ,
      ‖D‖^2 ≤ C*chartRealCovectorEnergy g.form a z D := by
  let S : Set ((ComplexVector n) × (ComplexVector n →L[ℝ] ℝ)) := K ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hContinuous : ContinuousOn (fun p : ComplexVector n × (ComplexVector n →L[ℝ] ℝ) =>
      chartRealCovectorEnergy g.form a p.1 p.2) S := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (((LeafProofs.L12Aux.realMetricFn_inverse_contDiffOn g a i j).continuousOn.comp continuousOn_fst
      (fun p hp => hKt hp.1)).mul
      (continuous_snd.clm_apply continuous_const).continuousOn).mul
      (continuous_snd.clm_apply continuous_const).continuousOn
  have hPositive (p : ComplexVector n × (ComplexVector n →L[ℝ] ℝ)) (hp : p ∈ S) :
      0 < chartRealCovectorEnergy g.form a p.1 p.2 := by
    apply chartRealCovectorEnergy_pos g.form a (hKt hp.1)
    have hNorm : ‖p.2‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.2
    intro hZero
    rw [hZero,norm_zero] at hNorm
    norm_num at hNorm
  obtain ⟨δ,hδ,hMin⟩ := hS.exists_forall_le' hContinuous hPositive
  refine ⟨δ⁻¹,inv_pos.mpr hδ,fun z hz D => ?_⟩
  by_cases hD : D=0
  · subst D
    simp [chartRealCovectorEnergy]
  have hNorm : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  have hUnit : (z,(‖D‖⁻¹ : ℝ) • D) ∈ S := by
    refine ⟨hz,?_⟩
    have hUnitNorm : ‖(‖D‖⁻¹ : ℝ) • D‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hNorm]
    simpa only [Metric.mem_sphere,dist_zero_right] using hUnitNorm
  have hMinD : δ ≤ chartRealCovectorEnergy g.form a z ((‖D‖⁻¹ : ℝ) • D) :=
    hMin (z,(‖D‖⁻¹ : ℝ) • D) hUnit
  have hScale : δ*‖D‖^2 ≤ chartRealCovectorEnergy g.form a z D := by
    have hCancel : ‖D‖^2*(‖D‖⁻¹)^2=1 := by rw [← mul_pow,mul_inv_cancel₀ hNorm,one_pow]
    calc
      _ ≤ ‖D‖^2*chartRealCovectorEnergy g.form a z ((‖D‖⁻¹ : ℝ) • D) := by
        simpa only [mul_comm δ] using mul_le_mul_of_nonneg_left hMinD (sq_nonneg ‖D‖)
      _ = _ := by rw [chartRealCovectorEnergy_smul,← mul_assoc,hCancel,one_mul]
  have hDiv : ‖D‖^2 ≤ chartRealCovectorEnergy g.form a z D/δ :=
    (le_div_iff₀ hδ).mpr (by simpa only [mul_comm δ] using hScale)
  simpa only [div_eq_mul_inv,mul_comm δ⁻¹] using hDiv

theorem compact_chart_fderiv_le_physical_gradient (g : SmoothMetric M) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hKt : K ⊆ chartTarget a) :
    ∃ C : ℝ,0 < C ∧ ∀ z ∈ K,∀ f : M.Carrier → ℝ,SmoothFn f →
      ‖fderiv ℝ (inChart a f) z‖ ≤ C*Real.sqrt (gradNormSq g.form f (chartInv a z)) := by
  obtain ⟨C,hC,hBound⟩ := compact_chart_real_covector_coercivity g a K hK hKt
  refine ⟨Real.sqrt (2*C),Real.sqrt_pos.mpr (by positivity),fun z hz f hf => ?_⟩
  have hEnergy := hBound z hz (fderiv ℝ (inChart a f) z)
  rw [chartRealCovectorEnergy_fderiv g.form a (hKt hz) hf] at hEnergy
  have hg0 : 0 ≤ gradNormSq g.form f (chartInv a z) := by
    have h := scalarGradientPair_self_nonneg g.form f (chartInv a z)
    rw [scalarGradientPair_eq_twice_gradNormSq g.form hf] at h
    linarith
  calc
    _ = Real.sqrt (‖fderiv ℝ (inChart a f) z‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((2*C)*gradNormSq g.form f (chartInv a z)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    _ = _ := Real.sqrt_mul (by positivity) _

end Yau.Proofs.F03Aux
