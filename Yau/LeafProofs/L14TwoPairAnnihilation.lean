import Yau.LeafProofs.L14TwoEnergyGlobal
import Yau.LeafProofs.L14ExhaustionCutoff

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

variable (hE : Holomorphic (r := r) E)
variable (f : NQForm E 1) (hf : LocallyL2 (r := r) E f) (hclosed : WeaklyClosed (r := r) E f)
  (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
  (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
    IsCompactJointTriple E g μ hμ h hh φ hφ t →
    inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
      inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)

include hE f hf hclosed u hrep in
theorem compact_joint_pair_annihilation_of_cutoffs
    (χ : ℕ → M.Carrier → ℝ) (hχ : ∀ m,SmoothFn (χ m)) (hcχ : ∀ m,HasCompactSupport (χ m))
    (hbχ : ∀ m x,χ m x ∈ Set.Icc (0 : ℝ) 1)
    (A : ℕ → ℝ) (hA : ∀ m,0 ≤ A m) (hgrad : ∀ m x,gradNormSq g.form (χ m) x ≤ A m)
    (htA : Tendsto A atTop (𝓝 0))
    (hcompact : ∀ K : Set M.Carrier,IsCompact K → ∀ᶠ m in atTop,∀ x ∈ K,χ m x = 1)
    (t : CompactJointTriple E g μ hμ h hh φ hφ) (ht : IsCompactJointTriple E g μ hμ h hh φ hφ t) :
    inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = 0 := by
  classical
  let U := t.1
  let D := t.2.2
  let K := closure {x | U.1 x ≠ (0 : NQForm E 1) x} ∪ closure {x | D.1 x ≠ (0 : NQForm E 2) x}
  have hK : IsCompact K := ht.2.1.union ht.2.2.2.2.2.1
  have hUD : WeakDbar (r := r) E U.1 D.1 := weakDbar_of_smooth_isDbarOf_degree E U.1 D.1 ht.1 ht.2.2.2.2.1 ht.2.2.2.2.2.2.1
  have hbound : ∀ᶠ m in atTop,
      ‖inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ D)‖^2 ≤
        (8*A m*‖w‖^2)*‖realizeWeightedOneSection E g μ hμ h hh φ hφ U‖^2 := by
    filter_upwards [hcompact K hK] with m hm
    obtain ⟨θ,hθ,_hcθ,hbθ,bθ,hsθ,hGθ,henergy⟩ := exists_compact_twoAdjoint_cutoff_energy E g μ hμ h hh φ hφ hE f hf hclosed u w hrep
      (χ m) (hχ m) (hcχ m) (hbχ m) (A m) (hA m) (hgrad m)
    have hUfix := weightedOneCutoff_realize_eq_of_one E g μ hμ h hh φ hφ (χ m) (hχ m) (hbχ m) U
      (fun x hx => hm x (Or.inl (subset_closure hx)))
    have hDfix := weightedTwoCutoff_realize_eq_of_one E g μ hμ h hh φ hφ θ hθ hbθ D (fun x hx => by
      have hχx : χ m x = 1 := hm x (Or.inr (subset_closure hx))
      have hxs : x ∈ tsupport (χ m) := subset_tsupport (χ m) (by change χ m x ≠ 0; rw [hχx];exact one_ne_zero)
      exact (show x ∈ {x | θ x = 1} from interior_subset (hsθ hxs)))
    have hgraph := hGθ U D hUD
    have htinner := weightedTwoCutoff_inner E g μ hμ h hh φ hφ θ hθ hbθ
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) w
    rw [hDfix] at htinner
    have he : inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) =
        inner ℂ (weightedOneCutoff E g μ hμ h hh φ hφ (χ m) (hχ m) (hbχ m) bθ)
          (realizeWeightedOneSection E g μ hμ h hh φ hφ U) := by
      have hec := congrArg star (htinner.trans hgraph)
      simp only [Complex.star_def,inner_conj_symm] at hec
      rw [hec,weightedOneCutoff_inner,hUfix]
    rw [he]
    have hn := norm_inner_le_norm (𝕜 := ℂ)
      (weightedOneCutoff E g μ hμ h hh φ hφ (χ m) (hχ m) (hbχ m) bθ)
      (realizeWeightedOneSection E g μ hμ h hh φ hφ U)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    rw [mul_pow] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right henergy (sq_nonneg _))
  have hr : Tendsto (fun m => (8*A m*‖w‖^2)*‖realizeWeightedOneSection E g μ hμ h hh φ hφ U‖^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using ((htA.const_mul 8).mul_const (‖w‖^2)).mul_const (‖realizeWeightedOneSection E g μ hμ h hh φ hφ U‖^2)
  have hz : ‖inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ D)‖^2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hr hbound
  have hn : ‖inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ D)‖ = 0 := by nlinarith [norm_nonneg (inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ D))]
  exact norm_eq_zero.mp hn


include hE f hf hclosed u hrep in
theorem compact_joint_pair_annihilation_with_center (o : M.Carrier)
    (t : CompactJointTriple E g μ hμ h hh φ hφ) (ht : IsCompactJointTriple E g μ hμ h hh φ hφ t) :
    inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = 0 := by
  obtain ⟨C,hC,χ,hχ,_hpoint,hcompact⟩ := exists_weightedDbar_cutoff_exhaustion_compact M g o
  let A := fun m : ℕ => (C/((m : ℝ)+1))^2/2
  have hA (m : ℕ) : 0 ≤ A m := by positivity
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun m : ℕ => C/((m : ℝ)+1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have htA : Tendsto A atTop (𝓝 0) := by simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div] using (hdiv.pow 2).div_const 2
  exact compact_joint_pair_annihilation_of_cutoffs E g μ hμ h hh φ hφ hE f hf hclosed u w hrep
    χ (fun m => (hχ m).1) (fun m => (hχ m).2.1) (fun m => (hχ m).2.2.1) A hA
    (fun m => (hχ m).2.2.2.2.2) htA hcompact t ht

include hE f hf hclosed u hrep in
theorem compact_joint_pair_annihilation
    (t : CompactJointTriple E g μ hμ h hh φ hφ) (ht : IsCompactJointTriple E g μ hμ h hh φ hφ t) :
    inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = 0 := by
  classical
  by_cases hM : Nonempty M.Carrier
  · exact compact_joint_pair_annihilation_with_center E g μ hμ h hh φ hφ hE f hf hclosed u w hrep (Classical.choice hM) t ht
  · haveI : IsEmpty M.Carrier := not_nonempty_iff.mp hM
    have hD : t.2.2 = (0 : WeightedTwoSection E g μ hμ h hh φ hφ) := by
      apply Subtype.ext
      funext x
      exact isEmptyElim x
    rw [hD]
    change inner ℂ w (0 : WeightedTwoHilbert E g μ hμ h hh φ hφ) = 0
    exact inner_zero_right _

end Yau.LeafProofs.L14Aux
