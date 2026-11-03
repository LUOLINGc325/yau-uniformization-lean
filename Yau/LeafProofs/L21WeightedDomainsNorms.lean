import Yau.LeafProofs.L21WeightedDomainsGraphCore

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedScalar_norm_sq (K : ℝ) (u : WeightedScalar n K) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂weightedBallMeasure n K := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem weightedScalar_tendsto_of_representative_errors (K : ℝ)
    {κ : Type*} {l : Filter κ} (u : κ → WeightedScalar n K) (v : WeightedScalar n K)
    (f : κ → X n → ℂ) (g : X n → ℂ)
    (hf : ∀ m, (u m : X n → ℂ) =ᵐ[weightedBallMeasure n K] f m)
    (hg : (v : X n → ℂ) =ᵐ[weightedBallMeasure n K] g)
    (h : Tendsto (fun m => ∫ x, ‖f m x-g x‖^2 ∂weightedBallMeasure n K) l (𝓝 0)) :
    Tendsto u l (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun m => ‖u m-v‖^2) l (𝓝 0) := by
    convert h using 1
    ext m
    rw [weightedScalar_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u m) v,hf m,hg] with x hx hfx hgx
    simp only [hx,Pi.sub_apply,hfx,hgx]
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs.sqrt

theorem weightedField_norm_sq (K : ℝ) {ι : Type*} [Fintype ι]
    (u : WeightedField n K ι) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂weightedBallMeasure n K := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem weightedField_norm_sq_eq_sum (K : ℝ) {ι : Type*} [Fintype ι]
    (u : WeightedField n K ι) :
    ‖u‖^2 = ∑ i, ∫ x, ‖u x i‖^2 ∂weightedBallMeasure n K := by
  rw [weightedField_norm_sq]
  simp_rw [EuclideanSpace.norm_sq_eq]
  apply integral_finsetSum
  intro i hi
  exact ((Lp.memLp u).eval_piLp i).integrable_norm_pow (by norm_num)

theorem weightedField_sub_norm_sq_eq_sum (K : ℝ) {ι : Type*} [Fintype ι]
    (u v : WeightedField n K ι) :
    ‖u-v‖^2 = ∑ i, ∫ x, ‖u x i-v x i‖^2 ∂weightedBallMeasure n K := by
  rw [weightedField_norm_sq_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with x hx
  rw [hx]
  rfl

theorem weightedField_tendsto_of_component_errors (K : ℝ)
    {ι κ : Type*} [Fintype ι] {l : Filter κ}
    (u : κ → WeightedField n K ι) (v : WeightedField n K ι)
    (h : ∀ i, Tendsto (fun m => ∫ x, ‖u m x i-v x i‖^2 ∂weightedBallMeasure n K) l (𝓝 0)) :
    Tendsto u l (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun m => ‖u m-v‖^2) l (𝓝 0) := by
    simpa only [weightedField_sub_norm_sq_eq_sum,Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => h i)
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs.sqrt

theorem weightedField_tendsto_of_representative_errors (K : ℝ)
    {ι κ : Type*} [Fintype ι] {l : Filter κ}
    (u : κ → WeightedField n K ι) (v : WeightedField n K ι)
    (f : κ → X n → ι → ℂ) (g : X n → ι → ℂ)
    (hf : ∀ m i, (fun x => u m x i) =ᵐ[weightedBallMeasure n K] (fun x => f m x i))
    (hg : ∀ i, (fun x => v x i) =ᵐ[weightedBallMeasure n K] (fun x => g x i))
    (h : ∀ i, Tendsto (fun m => ∫ x, ‖f m x i-g x i‖^2 ∂weightedBallMeasure n K) l (𝓝 0)) :
    Tendsto u l (𝓝 v) := by
  apply weightedField_tendsto_of_component_errors
  intro i
  convert h i using 1
  ext m
  apply integral_congr_ae
  filter_upwards [hf m i,hg i] with x hfx hgx
  rw [hfx,hgx]

theorem weightedCompactField_norm_sq (K : ℝ) (hK : 0 ≤ K)
    {ι : Type*} [Fintype ι] (u : ι → CompactTest (Metric.ball (0 : X n) 1)) :
    ‖weightedCompactField K hK u‖^2 = ∑ i, weightedScalarEnergy (boundaryWeight K) (u i) := by
  rw [weightedField_norm_sq_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← compactToWeightedScalar_norm_sq K hK (u i)]
  change _ = ‖(compactTest_weightedBall_memLp K hK (u i)).toLp (u i)‖^2
  rw [complex_toLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [weightedCompactField_coeFn K hK u] with x hx
  rw [hx]
  rfl

end Yau.LeafProofs.L21Aux
