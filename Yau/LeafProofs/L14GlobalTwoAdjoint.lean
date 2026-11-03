import Yau.LeafProofs.L14LocalTwoAdjoint
import Yau.LeafProofs.L14BoundedSquarePartition

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedTwoCutoff_sum
    {ι : Type*} [Fintype ι]
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hbχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (η : ι → M.Carrier → ℝ) (hη : ∀ i,SmoothFn (η i))
    (hbη : ∀ i x,η i x ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∀ x,∑ i,η i x = χ x)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    (∑ i,weightedTwoCutoff E g μ hμ h hh φ hφ (η i) (hη i) (hbη i) W) =
      weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbχ W := by
  classical
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih U =>
    change (∑ i,weightedTwoCutoff E g μ hμ h hh φ hφ (η i) (hη i) (hbη i)
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) = weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbχ (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)
    simp_rw [weightedTwoCutoff_realize]
    change (∑ i,UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (weightedTwoCutoffSection E g μ hμ h hh φ hφ (η i) (hη i) (hbη i) U)) =
      UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbχ U)
    rw [← map_sum]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    apply Subtype.ext
    rw [nqForm_sum_value]
    change (∑ i,(η i x : ℂ) • (U.1 x).1) = (χ x : ℂ) • (U.1 x).1
    rw [← Finset.sum_smul,← Complex.ofReal_sum,hsum]


variable (hE : Holomorphic (r := r) E)
include hE in
theorem exists_compact_weightedTwoAdjointGraph_cutoff
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  classical
  obtain ⟨s,p,hps,hpn,hpo,hpone,hple,hpsum,_⟩ := exists_finite_smooth_bundle_square_partition_bounded (r := r) E g hcχ
  let η := fun i : s => fun x => p i x^2*χ x
  have hηs (i : s) : SmoothFn (η i) := L18Aux.smoothFn_mul (L18Aux.smoothFn_pow (hps i).1 2) hχ
  have hηc (i : s) : HasCompactSupport (η i) := hcχ.mul_left
  have hηb (i : s) (x : M.Carrier) : η i x ∈ Set.Icc (0 : ℝ) 1 := by
    have h0 := hpn i x
    have h1 := hple i x
    have hχ0 := (hbound x).1
    have hχ1 := (hbound x).2
    have hsq : p i x^2 ≤ 1 := by nlinarith
    exact ⟨mul_nonneg (sq_nonneg _) hχ0,(mul_le_mul hsq hχ1 hχ0 (by norm_num)).trans_eq (one_mul 1)⟩
  have hηo (i : s) : tsupport (η i) ⊆ bundleChartSource (r := r) E (i : M.Carrier) := by
    apply (closure_mono (show Function.support (η i) ⊆ Function.support (p i) from ?_)).trans (hpo i)
    intro x hx hz
    exact hx (by simp only [η,hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul])
  have hsη (x : M.Carrier) : ∑ i,η i x = χ x := by
    dsimp only [η]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport χ
    · rw [(hpone x hx).self_of_nhds,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
  have hg (i : s) : ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ (η i) (hηs i) (hηb i) w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ :=
    exists_chart_weightedTwoAdjointGraph_cutoff E g μ hμ h hh φ hφ (i : M.Carrier) hE f hf u w hrep (η i) (hηs i) (hηc i) (hηb i) (hηo i)
  choose b hb using hg
  refine ⟨∑ i,b i,?_⟩
  have hsum := Submodule.sum_mem (weightedTwoAdjointGraph E g μ hμ h hh φ hφ) (fun i (_ : i ∈ Finset.univ) => hb i)
  have he : (∑ i,(weightedTwoCutoff E g μ hμ h hh φ hφ (η i) (hηs i) (hηb i) w,b i)) =
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w,∑ i,b i) := by
    rw [← prod_mk_sum,weightedTwoCutoff_sum E g μ hμ h hh φ hφ χ hχ hbound η hηs hηb hsη w]
  rwa [he] at hsum

end Yau.LeafProofs.L14Aux
