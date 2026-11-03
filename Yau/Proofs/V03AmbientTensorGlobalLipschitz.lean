import Yau.Proofs.V03AmbientTensorDescent
import Yau.Proofs.V03AmbientTensorLocalLipschitz
import Yau.Proofs.V03CompactChartNeighborhood
import Yau.Proofs.V03CompactAmbientGraph

/-! The single actual ambient tensor is uniformly Lipschitz on each
intrinsic compact set and the two complete closed time slabs. -/

open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def compactAmbientBoundaryTensor (d : VariationData X q) (j a : ℕ)
    (K : Set (CotangentPoint X.manifold))
    (p : CompactImmersionTimes d.G K d.T) : Matrix (Fin q) (Fin q) ℂ :=
  ambientBoundaryTensor d j a (compactImmersionPoint d.G p.1.1) p.1.2.1 p.2.1

theorem compactAmbientBoundaryTensor_locallyLipschitz {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K) :
    LocallyLipschitz (compactAmbientBoundaryTensor d j a K) := by
  intro p
  let y := compactImmersionPoint d.G p.1.1
  have hyK : y ∈ K := compactImmersionPoint_mem d.G _
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  obtain ⟨r, C, hr, hC, _, hbound⟩ := fixedAmbientBoundaryTensor_local_lipschitz
    hd j a y.1 (cotangentChart_mapsTo y.1 hy)
  obtain ⟨δ, hδ, hnear⟩ := compact_cotangent_chart_neighborhood hd.2.2.2.2.1 hK hyK y.1 hy hr
  let c : NNReal := ⟨3 * C, by positivity⟩
  refine ⟨c, Metric.ball p δ, Metric.ball_mem_nhds p hδ, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro p₁ hp₁ p₂ hp₂
  have hchart (p' : CompactImmersionTimes d.G K d.T) (hp' : p' ∈ Metric.ball p δ) :
      compactImmersionPoint d.G p'.1.1 ∈ cotangentSource y.1 ∧
      cotangentChart y.1 (compactImmersionPoint d.G p'.1.1) ∈
        Metric.ball (cotangentChart y.1 y) r := by
    apply hnear _ (compactImmersionPoint_mem d.G _)
    change ‖d.G (compactImmersionPoint d.G p'.1.1) -
      d.G (compactImmersionPoint d.G p.1.1)‖ < δ
    rw [compactImmersionPoint_image d.G p'.1.1, compactImmersionPoint_image d.G p.1.1]
    exact (compactImmersionTimes_spatial_dist_le p' p).trans_lt hp'
  have hc₁ := hchart p₁ hp₁
  have hc₂ := hchart p₂ hp₂
  have hb := hbound _ hc₁.2 _ hc₂.2 _ p₁.1.2.2 _ p₂.1.2.2 _ p₁.2.2 _ p₂.2.2
  rw [cotangentChart_left_inv y.1 hc₁.1, cotangentChart_left_inv y.1 hc₂.1,
    fixedAmbientBoundaryTensor_eq_ambient hd j a ha y.1 hc₁.1
      ⟨p₁.1.2.2.1, p₁.1.2.2.2.trans hd.2.1.le⟩,
    fixedAmbientBoundaryTensor_eq_ambient hd j a ha y.1 hc₂.1
      ⟨p₂.1.2.2.1, p₂.1.2.2.2.trans hd.2.1.le⟩,
    compactImmersionPoint_image d.G p₁.1.1,
    compactImmersionPoint_image d.G p₂.1.1] at hb
  have hsp := compactImmersionTimes_spatial_dist_le p₁ p₂
  have htm := compactImmersionTimes_physical_dist_le p₁ p₂
  have hct := compactImmersionTimes_center_dist_le p₁ p₂
  change dist (compactAmbientBoundaryTensor d j a K p₁)
    (compactAmbientBoundaryTensor d j a K p₂) ≤ (3 * C) * dist p₁ p₂
  rw [dist_eq_norm]
  change ‖ambientBoundaryTensor d j a (compactImmersionPoint d.G p₁.1.1) p₁.1.2.1 p₁.2.1 -
    ambientBoundaryTensor d j a (compactImmersionPoint d.G p₂.1.1) p₂.1.2.1 p₂.2.1‖ ≤ _
  exact hb.trans ((mul_le_mul_of_nonneg_left (by linarith :
    ‖p₁.1.1.1 - p₂.1.1.1‖ + |p₁.1.2.1 - p₂.1.2.1| + |p₁.2.1 - p₂.2.1| ≤
      3 * dist p₁ p₂) hC).trans_eq (by ring))

theorem ambientBoundaryTensor_compact_lipschitz {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ y' ∈ K,
      ∀ t ∈ Set.Icc 0 d.T, ∀ t' ∈ Set.Icc 0 d.T,
      ∀ s ∈ Set.Icc 0 d.T, ∀ s' ∈ Set.Icc 0 d.T,
      ‖ambientBoundaryTensor d j a y t s - ambientBoundaryTensor d j a y' t' s'‖ ≤
        C * (‖d.G y - d.G y'‖ + |t - t'| + |s - s'|) := by
  letI : CompactSpace (d.G '' K) := isCompact_iff_compactSpace.mp
    (cotangentCompact_ambient_isCompact hd.2.2.2.2.1.1 hK)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_univ : IsCompact (Set.univ : Set (CompactImmersionTimes d.G K d.T)))
    (compactAmbientBoundaryTensor_locallyLipschitz hd j a ha hK).locallyLipschitzOn
  refine ⟨C, C.2, fun y hy y' hy' t ht t' ht' s hs s' hs' => ?_⟩
  let p : CompactImmersionTimes d.G K d.T := ((⟨d.G y, ⟨y, hy, rfl⟩⟩, ⟨t, ht⟩), ⟨s, hs⟩)
  let p' : CompactImmersionTimes d.G K d.T := ((⟨d.G y', ⟨y', hy', rfl⟩⟩, ⟨t', ht'⟩), ⟨s', hs'⟩)
  have hh := hC.dist_le_mul p (Set.mem_univ _) p' (Set.mem_univ _)
  rw [dist_eq_norm] at hh
  change ‖ambientBoundaryTensor d j a
    (compactImmersionPoint d.G ⟨d.G y, ⟨y, hy, rfl⟩⟩) t s -
    ambientBoundaryTensor d j a
      (compactImmersionPoint d.G ⟨d.G y', ⟨y', hy', rfl⟩⟩) t' s'‖ ≤ _ at hh
  rw [compactImmersionPoint_eq hd.2.2.2.2.1.2.1 y hy,
    compactImmersionPoint_eq hd.2.2.2.2.1.2.1 y' hy'] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (compactImmersionTimes_dist_le_sum p p') C.2)

theorem ambientBoundaryTensor_compact_bound {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K, ∀ t ∈ Set.Icc 0 d.T, ∀ s ∈ Set.Icc 0 d.T,
      ‖ambientBoundaryTensor d j a y t s‖ ≤ M := by
  letI : CompactSpace (d.G '' K) := isCompact_iff_compactSpace.mp
    (cotangentCompact_ambient_isCompact hd.2.2.2.2.1.1 hK)
  obtain ⟨M, hM⟩ := ((isCompact_univ : IsCompact
    (Set.univ : Set (CompactImmersionTimes d.G K d.T))).image
      (compactAmbientBoundaryTensor_locallyLipschitz hd j a ha hK).continuous).isBounded.exists_norm_le
  refine ⟨max M 0, le_max_right _ _, fun y hy t ht s hs => ?_⟩
  let p : CompactImmersionTimes d.G K d.T := ((⟨d.G y, ⟨y, hy, rfl⟩⟩, ⟨t, ht⟩), ⟨s, hs⟩)
  have hh := hM (compactAmbientBoundaryTensor d j a K p) ⟨p, Set.mem_univ _, rfl⟩
  change ‖ambientBoundaryTensor d j a
    (compactImmersionPoint d.G ⟨d.G y, ⟨y, hy, rfl⟩⟩) t s‖ ≤ M at hh
  rw [compactImmersionPoint_eq hd.2.2.2.2.1.2.1 y hy] at hh
  exact hh.trans (le_max_left _ _)

end Yau.Blueprint.V03Proof
