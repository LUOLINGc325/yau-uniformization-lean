import Yau.LeafProofs.L14GlobalTwoAdjoint
import Yau.LeafProofs.L14LocalTwoEnergy
import Yau.LeafProofs.L14CompactPlateau
import Yau.LeafProofs.L14TwoCutoffProduct
import Yau.LeafProofs.L14CutoffEnergyAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
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

theorem exists_compact_weightedTwoAdjointGraph_cutoff_orthogonal
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (θ : M.Carrier → ℝ) (bθ : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hlocal : ∀ (a : M.Carrier) (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
      (hbη : ∀ x,η x ∈ Set.Icc (0 : ℝ) 1),
      tsupport η ⊆ bundleChartSource (r := r) E a → tsupport η ⊆ interior {x | θ x = 1} →
      ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
        (weightedTwoCutoff E g μ hμ h hh φ hφ η hη hbη w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ ∧ inner ℂ bθ b = 0)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ interior {x | θ x = 1}) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ ∧ inner ℂ bθ b = 0 := by
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
  have hηplateau (i : s) : tsupport (η i) ⊆ interior {x | θ x = 1} :=
    tsupport_mul_subset_right.trans hsχ
  have hg (i : s) : ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ (η i) (hηs i) (hηb i) w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ ∧ inner ℂ bθ b = 0 :=
    hlocal (i : M.Carrier) (η i) (hηs i) (hηc i) (hηb i) (hηo i) (hηplateau i)
  choose b hb hborth using hg
  refine ⟨∑ i,b i,?_,?_⟩
  · have hsum := Submodule.sum_mem (weightedTwoAdjointGraph E g μ hμ h hh φ hφ) (fun i (_ : i ∈ Finset.univ) => hb i)
    have he : (∑ i,(weightedTwoCutoff E g μ hμ h hh φ hφ (η i) (hηs i) (hηb i) w,b i)) =
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w,∑ i,b i) := by
      rw [← prod_mk_sum,weightedTwoCutoff_sum E g μ hμ h hh φ hφ χ hχ hbound η hηs hηb hsη w]
    rwa [he] at hsum

  · rw [inner_sum]
    simp only [hborth,Finset.sum_const_zero]


variable (hE : Holomorphic (r := r) E)
variable (f : NQForm E 1) (hf : LocallyL2 (r := r) E f) (hclosed : WeaklyClosed (r := r) E f)
  (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
  (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
    IsCompactJointTriple E g μ hμ h hh φ hφ t →
    inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
      inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)

include hE f hf hclosed u hrep in
theorem exists_compact_weightedTwoAdjointGraph_orthogonal
    (θ : M.Carrier → ℝ) (hθ : SmoothFn θ) (hbθ : ∀ x,θ x ∈ Set.Icc (0 : ℝ) 1)
    (bθ : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hGθ : (weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hbθ w,bθ) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hbχ : ∀ x,χ x ∈ Set.Icc (0 : ℝ) 1) (hsχ : tsupport χ ⊆ interior {x | θ x = 1}) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbχ w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ ∧ inner ℂ bθ b = 0 := by
  apply exists_compact_weightedTwoAdjointGraph_cutoff_orthogonal E g μ hμ h hh φ hφ w θ bθ _ χ hχ hcχ hbχ hsχ
  intro a η hη hcη hbη hsη hsθη
  obtain ⟨K,hK,hKO,hsK,hθK⟩ := exists_compact_chart_model_set_in_plateau E a θ η hη hcη hsη hsθη
  exact exists_local_weightedTwoAdjointGraph_orthogonal E g μ hμ h hh φ hφ hE f hf hclosed u w hrep θ hθ hbθ bθ hGθ a K hK hKO η hη hcη hbη hsη hsK hθK

include hE f hf hclosed u hrep in
theorem exists_compact_twoAdjoint_cutoff_energy
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hbχ : ∀ x,χ x ∈ Set.Icc (0 : ℝ) 1)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x,gradNormSq g.form χ x ≤ C) :
    ∃ (θ : M.Carrier → ℝ) (hθ : SmoothFn θ) (hcθ : HasCompactSupport θ)
      (hbθ : ∀ x,θ x ∈ Set.Icc (0 : ℝ) 1) (bθ : WeightedOneHilbert E g μ hμ h hh φ hφ),
      tsupport χ ⊆ interior {x | θ x = 1} ∧
      (weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hbθ w,bθ) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ ∧
      ‖weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbχ bθ‖^2 ≤ 8*C*‖w‖^2 := by
  obtain ⟨θ,hθ,hcθ,hbθ,hsθ⟩ := exists_smooth_compact_plateau g hcχ
  obtain ⟨bθ,hGθ⟩ := exists_compact_weightedTwoAdjointGraph_cutoff E g μ hμ h hh φ hφ hE f hf u w hrep θ hθ hcθ hbθ
  refine ⟨θ,hθ,hcθ,hbθ,bθ,hsθ,hGθ,?_⟩
  let χsq := fun x => χ x^2
  have hsχsq : tsupport χsq ⊆ tsupport χ := tsupport_comp_subset (g := fun t : ℝ => t^2) (by norm_num) χ
  have hχsq : SmoothFn χsq := fun a => (hχ a).pow 2
  have hbχsq : ∀ x,χsq x ∈ Set.Icc (0 : ℝ) 1 := cutoff_sq_mem_Icc χ hbχ
  have hone (x : M.Carrier) (hx : x ∈ tsupport χ) : θ x = 1 := (show x ∈ {x | θ x = 1} from interior_subset (hsθ hx))
  have honesq (x : M.Carrier) (hx : x ∈ tsupport χsq) : θ x = 1 := hone x (hsχsq hx)
  obtain ⟨b,hGb,horth⟩ := exists_compact_weightedTwoAdjointGraph_orthogonal E g μ hμ h hh φ hφ hE f hf hclosed u w hrep
    θ hθ hbθ bθ hGθ χsq hχsq (hcχ.of_isClosed_subset (isClosed_tsupport _) hsχsq) hbχsq (hsχsq.trans hsθ)
  have hprod := weightedTwoAdjointGraph_cutoff E g μ hμ h hh φ hφ χsq hχsq hbχsq (4*C) (by positivity)
    (gradNormSq_cutoff_sq_le g.form χ hχ hbχ C hC hgrad) (weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hbθ w) bθ hGθ
  rw [weightedTwoCutoff_comp_eq_of_one E g μ hμ h hh φ hφ χsq θ hχsq hθ hbχsq hbθ honesq w,
    weightedTwoHilbertGradientContraction_cutoff_eq_of_one E g μ hμ h hh φ hφ χsq θ hχsq hθ hbθ (4*C) (by positivity)
      (gradNormSq_cutoff_sq_le g.form χ hχ hbχ C hC hgrad) honesq w] at hprod
  change (weightedTwoCutoff E g μ hμ h hh φ hφ χsq hχsq hbχsq w,
    weightedOneCutoff E g μ hμ h hh φ hφ χsq hχsq hbχsq bθ-
    weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ (fun x => χ x^2) (fun a => (hχ a).pow 2) (4*C) (by positivity)
      (gradNormSq_cutoff_sq_le g.form χ hχ hbχ C hC hgrad) w) ∈ _ at hprod
  rw [weightedTwoHilbertGradientContraction_cutoff_sq E g μ hμ h hh φ hφ χ hχ hbχ C hC hgrad w,← weightedOneCutoff_sq E g μ hμ h hh φ hφ χ hχ hbχ bθ] at hprod
  have heq := weightedTwoAdjointGraph_single_valued E g μ hμ h hh φ hφ hE _ _ _ hprod hGb
  have hpair : (inner ℂ bθ
      (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbχ (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbχ bθ)-
        (2 : ℂ) • weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbχ
          (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad w))).re = 0 := by
    rw [heq,horth]
    rfl
  exact cutoff_energy_estimate_of_two_mul
    (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbχ)
    (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad) bθ w C
    (fun x y => (weightedOneCutoff_inner E g μ hμ h hh φ hφ χ hχ hbχ x y).symm) hpair hC
    (weightedTwoHilbertGradientContraction_norm_sq_le E g μ hμ h hh φ hφ χ hχ C hC hgrad w)

end Yau.LeafProofs.L14Aux
