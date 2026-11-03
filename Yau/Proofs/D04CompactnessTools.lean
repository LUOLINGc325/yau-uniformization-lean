import Yau.Proofs.D04Convolution
import Yau.LeafProofs.L08

open MeasureTheory Filter
open scoped Topology ContDiff Convolution BoundedContinuousFunction

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau

variable {d : ℕ}

/-! Quantitative smoothing, Arzelà–Ascoli, and compact exhaustion in the
actual complex dimension. Dimension-independent L¹ lemmas are reused from
L08 with their original generic statements. -/

theorem integrable_radialConvolution_integrand {t : ℝ} (ht : 0 < t)
    {g : (ComplexVector d) → ℝ} (hg : Integrable g volume) (z : (ComplexVector d)) :
    Integrable (fun w ↦ radialKernel (n := d) t (z - w) * g w) volume := by
  obtain ⟨A, hA⟩ := (radialKernel_hasCompactSupport (n := d) ht).exists_bound_of_continuous
    (contDiff_radialKernel (n := d) t).continuous
  exact hg.bdd_mul
    ((contDiff_radialKernel (n := d) t).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w ↦ hA (z - w))

theorem radialConvolution_norm_le {t : ℝ} (_ht : 0 < t)
    {g : (ComplexVector d) → ℝ} (hg : Integrable g volume) {A : ℝ}
    (hA : ∀ w, ‖radialKernel (n := d) t w‖ ≤ A) (z : (ComplexVector d)) :
    ‖∫ w, radialKernel (n := d) t (z - w) * g w‖ ≤ A * ∫ w, |g w| := by
  have h := norm_integral_le_of_norm_le (hg.norm.const_mul A)
    (Filter.Eventually.of_forall fun w ↦
      (norm_mul (radialKernel (n := d) t (z - w)) (g w)).le.trans
        (mul_le_mul_of_nonneg_right (hA (z - w)) (norm_nonneg _)))
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

/-- At a fixed scale, an L¹ bound gives a common Lipschitz constant for
all the smoothed functions. -/
theorem radialConvolution_lipschitz {t : ℝ} (ht : 0 < t)
    {g : (ComplexVector d) → ℝ} (hg : Integrable g volume) {C : NNReal}
    (hC : LipschitzWith C (radialKernel (n := d) t)) {M : ℝ} (hM : 0 ≤ M)
    (hgM : (∫ w, |g w|) ≤ M) :
    LipschitzWith (C * M.toNNReal) (fun z : (ComplexVector d) ↦ ∫ w, radialKernel (n := d) t (z - w) * g w) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [dist_eq_norm, ← integral_sub (integrable_radialConvolution_integrand ht hg z)
    (integrable_radialConvolution_integrand ht hg z')]
  have hb (w : (ComplexVector d)) :
      ‖radialKernel (n := d) t (z - w) * g w - radialKernel (n := d) t (z' - w) * g w‖ ≤
        ((C : ℝ) * dist z z') * ‖g w‖ := by
    have h := hC.dist_le_mul (z - w) (z' - w)
    rw [dist_sub_right] at h
    rw [dist_eq_norm] at h
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have hn := norm_integral_le_of_norm_le (hg.norm.const_mul ((C : ℝ) * dist z z'))
    (Filter.Eventually.of_forall hb)
  rw [integral_const_mul] at hn
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hgM (by positivity : 0 ≤ (C : ℝ) * dist z z'))
  simp only [NNReal.coe_mul, Real.coe_toNNReal M hM]
  convert hn' using 1; ring

theorem radialConvolution_uniform_bounds {t : ℝ} (ht : 0 < t)
    {g : ℕ → (ComplexVector d) → ℝ} (hg : ∀ j, Integrable (g j) volume)
    {B : ℝ} (hB : ∀ j, (∫ w, |g j w|) ≤ B) :
    ∃ (A : ℝ) (C : NNReal), 0 ≤ A ∧
      (∀ j z, |∫ w, radialKernel (n := d) t (z - w) * g j w| ≤ A) ∧
      (∀ j, LipschitzWith C (fun z : (ComplexVector d) ↦ ∫ w, radialKernel (n := d) t (z - w) * g j w)) := by
  obtain ⟨D, hD⟩ := (radialKernel_hasCompactSupport (n := d) ht).exists_bound_of_continuous
    (contDiff_radialKernel (n := d) t).continuous
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (radialKernel_hasCompactSupport (n := d) ht) (contDiff_radialKernel (n := d) t) (by simp)
  refine ⟨max D 0 * max B 0, L * (max B 0).toNNReal, by positivity, ?_, ?_⟩
  · intro j z
    have h := radialConvolution_norm_le ht (hg j)
      (fun w ↦ (hD w).trans (le_max_left D 0)) z
    exact h.trans (mul_le_mul_of_nonneg_left ((hB j).trans (le_max_left B 0)) (le_max_right D 0))
  · intro j
    exact radialConvolution_lipschitz ht (hg j) hLip (le_max_right B 0)
      ((hB j).trans (le_max_left B 0))

/-- Arzelà–Ascoli in the explicit uniform-Cauchy form used below. -/
theorem uniformlyCauchy_subseq_of_bounded_lipschitz {K : Set (ComplexVector d)} (hK : IsCompact K)
    {f : ℕ → (ComplexVector d) → ℝ} {A : ℝ} {C : NNReal}
    (hA : ∀ j z, z ∈ K → |f j z| ≤ A) (hLip : ∀ j, LipschitzWith C (f j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, ∀ z ∈ K, |f (σ i) z - f (σ j) z| < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → (K →ᵇ ℝ) := fun j ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ f j z, (hLip j).continuous.comp continuous_subtype_val⟩
  have hLF (j : ℕ) : LipschitzWith C (F j) := by
    have h := (hLip j).comp (LipschitzWith.subtype_val K)
    rw [mul_one] at h
    convert h using 1
    funext z
    exact BoundedContinuousFunction.mkOfCompact_apply _ z
  have heq : Equicontinuous ((↑) : Set.range F → K → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ C
    intro h
    obtain ⟨j, hj⟩ := h.2
    rw [← hj]
    exact hLF j
  have hc : IsCompact (closure (Set.range F)) := BoundedContinuousFunction.arzela_ascoli
    (Set.Icc (-A) A) isCompact_Icc (Set.range F)
    (fun h z hh ↦ by
      obtain ⟨j, rfl⟩ := hh
      exact abs_le.mp (hA j z z.2)) heq
  obtain ⟨v, _, σ, hσ, hconv⟩ := hc.tendsto_subseq (fun j ↦ subset_closure (Set.mem_range_self j))
  refine ⟨σ, hσ, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro i hi j hj z hz
  have hi' : dist (F (σ i)) v < ε / 2 := hN i hi
  have hj' : dist (F (σ j)) v < ε / 2 := hN j hj
  have hdist : dist (F (σ i)) (F (σ j)) < ε := by
    have := dist_triangle_right (F (σ i)) (F (σ j)) v
    linarith
  have hp := BoundedContinuousFunction.dist_coe_le_dist (f := F (σ i)) (g := F (σ j))
    (⟨z, hz⟩ : K)
  change |f (σ i) z - f (σ j) z| ≤ dist (F (σ i)) (F (σ j)) at hp
  exact hp.trans_lt hdist


/-- A single subsequence is uniformly Cauchy for a countable collection of
bounded equicontinuous families on compact subsets. -/
theorem uniformlyCauchy_subseq_countable {ι : Type*} [Countable ι]
    (K : ι → Set (ComplexVector d)) (hK : ∀ m, IsCompact (K m))
    (f : ι → ℕ → (ComplexVector d) → ℝ) (A : ι → ℝ) (C : ι → NNReal)
    (hA : ∀ m j z, z ∈ K m → |f m j z| ≤ A m)
    (hLip : ∀ m j, LipschitzWith (C m) (f m j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ m ε, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, ∀ z ∈ K m, |f m (σ i) z - f m (σ j) z| < ε := by
  let (m : ι) : CompactSpace (K m) := isCompact_iff_compactSpace.mp (hK m)
  let F : ∀ m : ι, ℕ → ((K m) →ᵇ ℝ) := fun m j ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ f m j z, (hLip m j).continuous.comp continuous_subtype_val⟩
  have hLF (m : ι) (j : ℕ) : LipschitzWith (C m) (F m j) := by
    have h := (hLip m j).comp (LipschitzWith.subtype_val (K m))
    rw [mul_one] at h
    convert h using 1
    funext z
    exact BoundedContinuousFunction.mkOfCompact_apply _ z
  have hcompact (m : ι) : IsCompact (closure (Set.range (F m))) :=
    Yau.LeafProofs.L08_isCompact_closure_bounded_lipschitz (F m) (fun j z ↦ hA m j z z.2) (hLF m)
  let P := ∀ m : ι, {v : (K m) →ᵇ ℝ // v ∈ closure (Set.range (F m))}
  let (m : ι) : CompactSpace {v : (K m) →ᵇ ℝ // v ∈ closure (Set.range (F m))} :=
    isCompact_iff_compactSpace.mp (hcompact m)
  let p : ℕ → P := fun j m ↦ ⟨F m j, subset_closure (Set.mem_range_self j)⟩
  obtain ⟨v, σ, hσ, hconv⟩ := CompactSpace.tendsto_subseq p
  refine ⟨σ, hσ, ?_⟩
  intro m ε hε
  have hproj : Continuous (fun q : P ↦ (q m).1) := continuous_subtype_val.comp (continuous_apply m)
  have hmconv := (hproj.tendsto v).comp hconv
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmconv (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro i hi j hj z hz
  have hi' : dist (F m (σ i)) (v m).1 < ε / 2 := hN i hi
  have hj' : dist (F m (σ j)) (v m).1 < ε / 2 := hN j hj
  have hdist : dist (F m (σ i)) (F m (σ j)) < ε := by
    have := dist_triangle_right (F m (σ i)) (F m (σ j)) (v m).1
    linarith
  have hp := BoundedContinuousFunction.dist_coe_le_dist (f := F m (σ i)) (g := F m (σ j))
    (⟨z, hz⟩ : K m)
  change |f m (σ i) z - f m (σ j) z| ≤ dist (F m (σ i)) (F m (σ j)) at hp
  exact hp.trans_lt hdist


theorem dist_toL1_on_le_const {K : Set (ComplexVector d)} (hK : IsCompact K)
    {f g : (ComplexVector d) → ℝ} (hf : IntegrableOn f K volume) (hg : IntegrableOn g K volume)
    {ε : ℝ} (hε : ∀ z ∈ K, |f z - g z| ≤ ε) :
    dist (hf.toL1 f) (hg.toL1 g) ≤ ε * volume.real K := by
  change Integrable f (volume.restrict K) at hf
  change Integrable g (volume.restrict K) at hg
  rw [Yau.LeafProofs.L08_dist_toL1_eq_integral_abs]
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (ComplexVector d)))
    (s := K) (f := fun z ↦ |f z - g z|) hK.measure_lt_top
    (fun z hz ↦ (by simpa only [Real.norm_eq_abs, abs_abs] using hε z hz : ‖|f z - g z|‖ ≤ ε))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)] using h

theorem integral_abs_indicator (f : (ComplexVector d) → ℝ) {S : Set (ComplexVector d)} (hS : MeasurableSet S) :
    (∫ w, |S.indicator f w|) = ∫ w in S, |f w| := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw]
  · simp only [Set.indicator_of_notMem hw, abs_zero]

/-- Every coordinate open set has a nested sequence of compact subsets that
eventually contains each compact subset of the open set. -/
theorem exists_compact_exhaustion {O : Set (ComplexVector d)} (hO : IsOpen O) :
    ∃ K : ℕ → Set (ComplexVector d), (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ O) ∧ Monotone K ∧
      ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ n, S ⊆ K n := by
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let E := CompactExhaustion.choice O
  let K : ℕ → Set (ComplexVector d) := fun n ↦ (Subtype.val : O → (ComplexVector d)) '' E n
  refine ⟨K, fun n ↦ (E.isCompact n).image continuous_subtype_val, ?_, ?_, ?_⟩
  · intro n z hz
    obtain ⟨w, _, rfl⟩ := hz
    exact w.2
  · intro n m hnm
    exact Set.image_mono (E.subset hnm)
  · intro S hS hSO
    have hpre : IsCompact ((Subtype.val : O → (ComplexVector d)) ⁻¹' S) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rw [Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hSO)]
      exact hS
    obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hpre
    refine ⟨n, ?_⟩
    intro z hz
    exact ⟨⟨z, hSO hz⟩, hn hz, rfl⟩


theorem integral_abs_le_const {K : Set (ComplexVector d)} (hK : IsCompact K)
    {f : (ComplexVector d) → ℝ} {ε : ℝ} (hε : ∀ z ∈ K, |f z| ≤ ε) :
    (∫ z in K, |f z|) ≤ ε * volume.real K := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (ComplexVector d)))
    (s := K) (f := fun z ↦ |f z|) hK.measure_lt_top
    (fun z hz ↦ (by simpa only [Real.norm_eq_abs, abs_abs] using hε z hz : ‖|f z|‖ ≤ ε))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)] using h

end Yau.Proofs.D04Aux
