import Yau.Proofs.V03CompactImmersionCoefficient

/-! Smooth coefficients on the actual cotangent charts have uniform
Lipschitz control in the immersion distance and both complete time slabs. -/

open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem timeCoefficient_local_lipschitz {d : VariationData X q} (hd : VariationSetup d)
    {b : CotangentPoint X.manifold → ℝ → ℝ → F}
    (hb : ∀ x, ContDiffOn ℝ ∞
      (fun p : (CotangentCoord n × ℝ) × ℝ => b (cotangentChartInv x p.1.1) p.1.2 p.2)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ))
    (x : X.manifold.Carrier) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ Metric.ball z r ⊆ cotangentTarget x ∧
      ∀ u ∈ Metric.ball z r, ∀ v ∈ Metric.ball z r,
      ∀ t ∈ Set.Icc 0 d.T, ∀ t' ∈ Set.Icc 0 d.T,
      ∀ s ∈ Set.Icc 0 d.T, ∀ s' ∈ Set.Icc 0 d.T,
        ‖b (cotangentChartInv x u) t s - b (cotangentChartInv x v) t' s'‖ ≤
          C * (‖d.G (cotangentChartInv x u) - d.G (cotangentChartInv x v)‖ +
            |t - t'| + |s - s'|) := by
  obtain ⟨r, C₀, hr, hC₀, hrS, hlow⟩ := cotangentImmersion_local_chart_bound
    hd.2.2.2.2.1 x hz
  let S := ((Metric.closedBall z (r / 2) ×ˢ Set.Icc 0 d.T) ×ˢ Set.Icc 0 d.T)
  have hball : Metric.closedBall z (r / 2) ⊆ Metric.ball z r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  have hsub : S ⊆ ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) := by
    intro p hp
    exact ⟨⟨hrS (hball hp.1.1), ⟨hp.1.2.1, hp.1.2.2.trans hd.2.1.le⟩⟩, Set.mem_univ _⟩
  obtain ⟨K, hK⟩ := ((hb x).mono hsub).exists_lipschitzOnWith (by simp)
    (((convex_closedBall z (r / 2)).prod (convex_Icc 0 d.T)).prod (convex_Icc 0 d.T))
    (((isCompact_closedBall z (r / 2)).prod isCompact_Icc).prod isCompact_Icc)
  refine ⟨r / 2, (K : ℝ) * (C₀ + 1), half_pos hr,
    mul_nonneg K.2 (by linarith), ?_, ?_⟩
  · exact (Metric.ball_subset_ball (half_le_self hr.le)).trans hrS
  intro u hu v hv t ht t' ht' s hs s' hs'
  have hu' := Metric.ball_subset_closedBall hu
  have hv' := Metric.ball_subset_closedBall hv
  have hlu := hlow u (hball hu') v (hball hv')
  have hdist := hK.dist_le_mul ((u, t), s) ⟨⟨hu', ht⟩, hs⟩
    ((v, t'), s') ⟨⟨hv', ht'⟩, hs'⟩
  have hmax : dist ((u, t), s) ((v, t'), s') ≤ ‖u - v‖ + |t - t'| + |s - s'| := by
    rw [Prod.dist_eq, Prod.dist_eq, dist_eq_norm u v, Real.dist_eq, Real.dist_eq]
    exact max_le (max_le (by linarith [abs_nonneg (t - t'), abs_nonneg (s - s')])
      (by linarith [norm_nonneg (u - v), abs_nonneg (s - s')]))
      (by linarith [norm_nonneg (u - v), abs_nonneg (t - t')])
  have hsum : ‖u - v‖ + |t - t'| + |s - s'| ≤
      (C₀ + 1) * (‖d.G (cotangentChartInv x u) - d.G (cotangentChartInv x v)‖ +
        |t - t'| + |s - s'|) := by
    nlinarith [norm_nonneg (d.G (cotangentChartInv x u) - d.G (cotangentChartInv x v)),
      abs_nonneg (t - t'), abs_nonneg (s - s')]
  rw [dist_eq_norm] at hdist
  simpa only [mul_assoc] using
    hdist.trans (mul_le_mul_of_nonneg_left (hmax.trans hsum) K.2)

def compactTimeCoefficient (d : VariationData X q)
    (b : CotangentPoint X.manifold → ℝ → ℝ → F) (K : Set (CotangentPoint X.manifold))
    (p : CompactImmersionTimes d.G K d.T) : F :=
  b (compactImmersionPoint d.G p.1.1) p.1.2.1 p.2.1

theorem compactTimeCoefficient_locallyLipschitz {d : VariationData X q}
    (hd : VariationSetup d) {b : CotangentPoint X.manifold → ℝ → ℝ → F}
    (hb : ∀ x, ContDiffOn ℝ ∞
      (fun p : (CotangentCoord n × ℝ) × ℝ => b (cotangentChartInv x p.1.1) p.1.2 p.2)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ))
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K) :
    LocallyLipschitz (compactTimeCoefficient d b K) := by
  intro p
  let y := compactImmersionPoint d.G p.1.1
  have hyK : y ∈ K := compactImmersionPoint_mem d.G _
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  obtain ⟨r, C, hr, hC, _, hbound⟩ := timeCoefficient_local_lipschitz
    hd hb y.1 (cotangentChart_mapsTo y.1 hy)
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
  have hbound' := hbound _ hc₁.2 _ hc₂.2 _ p₁.1.2.2 _ p₂.1.2.2 _ p₁.2.2 _ p₂.2.2
  rw [cotangentChart_left_inv y.1 hc₁.1, cotangentChart_left_inv y.1 hc₂.1,
    compactImmersionPoint_image d.G p₁.1.1,
    compactImmersionPoint_image d.G p₂.1.1] at hbound'
  have hsp := compactImmersionTimes_spatial_dist_le p₁ p₂
  have htm := compactImmersionTimes_physical_dist_le p₁ p₂
  have hct := compactImmersionTimes_center_dist_le p₁ p₂
  rw [dist_eq_norm]
  change ‖b (compactImmersionPoint d.G p₁.1.1) p₁.1.2.1 p₁.2.1 -
    b (compactImmersionPoint d.G p₂.1.1) p₂.1.2.1 p₂.2.1‖ ≤ (3 * C) * dist p₁ p₂
  exact hbound'.trans ((mul_le_mul_of_nonneg_left (by linarith :
    ‖p₁.1.1.1 - p₂.1.1.1‖ + |p₁.1.2.1 - p₂.1.2.1| + |p₁.2.1 - p₂.2.1| ≤
      3 * dist p₁ p₂) hC).trans_eq (by ring))

theorem timeCoefficient_compact_lipschitz {d : VariationData X q} (hd : VariationSetup d)
    {b : CotangentPoint X.manifold → ℝ → ℝ → F}
    (hb : ∀ x, ContDiffOn ℝ ∞
      (fun p : (CotangentCoord n × ℝ) × ℝ => b (cotangentChartInv x p.1.1) p.1.2 p.2)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ))
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ y' ∈ K,
      ∀ t ∈ Set.Icc 0 d.T, ∀ t' ∈ Set.Icc 0 d.T,
      ∀ s ∈ Set.Icc 0 d.T, ∀ s' ∈ Set.Icc 0 d.T,
      ‖b y t s - b y' t' s'‖ ≤ C * (‖d.G y - d.G y'‖ + |t - t'| + |s - s'|) := by
  letI : CompactSpace (d.G '' K) := isCompact_iff_compactSpace.mp
    (cotangentCompact_ambient_isCompact hd.2.2.2.2.1.1 hK)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_univ : IsCompact (Set.univ : Set (CompactImmersionTimes d.G K d.T)))
    (compactTimeCoefficient_locallyLipschitz hd hb hK).locallyLipschitzOn
  refine ⟨C, C.2, fun y hy y' hy' t ht t' ht' s hs s' hs' => ?_⟩
  let p : CompactImmersionTimes d.G K d.T := ((⟨d.G y, ⟨y, hy, rfl⟩⟩, ⟨t, ht⟩), ⟨s, hs⟩)
  let p' : CompactImmersionTimes d.G K d.T := ((⟨d.G y', ⟨y', hy', rfl⟩⟩, ⟨t', ht'⟩), ⟨s', hs'⟩)
  have hh := hC.dist_le_mul p (Set.mem_univ _) p' (Set.mem_univ _)
  rw [dist_eq_norm] at hh
  change ‖b (compactImmersionPoint d.G ⟨d.G y, ⟨y, hy, rfl⟩⟩) t s -
    b (compactImmersionPoint d.G ⟨d.G y', ⟨y', hy', rfl⟩⟩) t' s'‖ ≤ _ at hh
  rw [compactImmersionPoint_eq hd.2.2.2.2.1.2.1 y hy,
    compactImmersionPoint_eq hd.2.2.2.2.1.2.1 y' hy'] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (compactImmersionTimes_dist_le_sum p p') C.2)

end Yau.Blueprint.V04Proof
