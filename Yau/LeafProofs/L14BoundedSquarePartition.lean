import Yau.LeafProofs.L14SquarePartition

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A finite square partition near a compact set, with globally bounded weights and
square sum. Each weight and its genuine bundle-chart pullback are smooth and
compactly supported in the corresponding chart domains. -/
theorem exists_finite_smooth_bundle_square_partition_bounded (g : Yau.SmoothMetric M)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ s : Finset M.Carrier, ∃ χ : s → M.Carrier → ℝ,
      (∀ i, SmoothFn (χ i) ∧ HasCompactSupport (χ i)) ∧
        (∀ i x, 0 ≤ χ i x) ∧
        (∀ i, tsupport (χ i) ⊆ bundleChartSource (r := r) E (i : M.Carrier)) ∧
        (∀ x ∈ K, ∀ᶠ y in 𝓝 x, ∑ i, χ i y ^ 2 = 1) ∧
        (∀ i x, χ i x ≤ 1) ∧
        (∀ x, ∑ i, χ i x ^ 2 ≤ 1) ∧
        (∀ i : s, ContDiff ℝ ∞ (L18Aux.chartPullbackZero (i : M.Carrier) (χ i)) ∧
          HasCompactSupport (L18Aux.chartPullbackZero (i : M.Carrier) (χ i)) ∧
          tsupport (L18Aux.chartPullbackZero (i : M.Carrier) (χ i)) ⊆
            localDomain (r := r) E (i : M.Carrier)) := by
  classical
  letI : MetricSpace M.Carrier := L12Aux.inducedMetricSpace g
  letI := L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  obtain ⟨s, p, hps, hpn, hpo, hpone⟩ := exists_finite_smooth_bundle_partition (r := r) E hL
  obtain ⟨η, hηone, hηzero, hηrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, ComplexVector n)) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hηs : SmoothFn (fun x => η x) := L18Aux.smoothFn_of_contMDiff_real η.contMDiff
  have hηsupp : Function.support η ⊆ L := by
    intro x hx
    by_contra hn
    exact hx (hηzero x hn)
  have hηc : HasCompactSupport η :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal hηsupp hL.isClosed)
  let P := fun x => ∑ i, p i x
  let A := fun x => ∑ i, p i x ^ 2
  let D := fun x => A x + (1 - P x) ^ 2
  have hAn (x : M.Carrier) : 0 ≤ A x := Finset.sum_nonneg (fun i _ => sq_nonneg (p i x))
  have hDpos (x : M.Carrier) : 0 < D x := by
    by_cases hAp : 0 < A x
    · exact add_pos_of_pos_of_nonneg hAp (sq_nonneg _)
    · have hAz : A x = 0 := le_antisymm (le_of_not_gt hAp) (hAn x)
      have hpz (i : s) : p i x = 0 := by
        have hle : p i x ^ 2 ≤ A x :=
          Finset.single_le_sum (fun j _ => sq_nonneg (p j x)) (Finset.mem_univ i)
        rw [hAz] at hle
        nlinarith [sq_nonneg (p i x)]
      have hPz : P x = 0 := by simp only [P, hpz, Finset.sum_const_zero]
      change 0 < A x + (1 - P x) ^ 2
      rw [hAz, hPz]
      norm_num
  have hPs : SmoothFn P := L18Aux.smoothFn_sum p hps
  have hAs : SmoothFn A := L18Aux.smoothFn_sum (fun i x => p i x ^ 2)
    (fun i => L18Aux.smoothFn_pow (hps i) 2)
  have hDs : SmoothFn D := by
    intro a
    exact (hAs a).add ((contDiffOn_const.sub (hPs a)).pow 2)
  let χ := fun i : s => fun x => η x * (p i x / Real.sqrt (D x))
  have hχs (i : s) : SmoothFn (χ i) ∧ HasCompactSupport (χ i) := by
    refine ⟨?_, hηc.mul_right⟩
    intro a
    exact (hηs a).mul ((hps i a).div ((hDs a).sqrt
      (fun z _ => ne_of_gt (hDpos (chartInv a z))))
        (fun z _ => Real.sqrt_ne_zero'.mpr (hDpos (chartInv a z))))
  have hχn (i : s) (x : M.Carrier) : 0 ≤ χ i x := by
    exact mul_nonneg (hηrange x).1 (div_nonneg (hpn i x) (Real.sqrt_nonneg _))
  have hχo (i : s) : tsupport (χ i) ⊆ bundleChartSource (r := r) E (i : M.Carrier) := by
    apply (closure_mono (show Function.support (χ i) ⊆ Function.support (p i) from ?_)).trans (hpo i)
    intro x hx hpzero
    apply hx
    simp only [χ, hpzero, zero_div, mul_zero]
  have hχsum (x : M.Carrier) : ∑ i, χ i x ^ 2 ≤ 1 := by
    have hηsq : η x ^ 2 ≤ 1 := (sq_le_one_iff₀ (hηrange x).1).2 (hηrange x).2
    have hAD : A x ≤ D x := le_add_of_nonneg_right (sq_nonneg _)
    calc
      ∑ i, χ i x ^ 2 = η x ^ 2 * (A x / D x) := by
        simp only [χ, mul_pow, div_pow, Real.sq_sqrt (hDpos x).le]
        rw [← Finset.mul_sum, ← Finset.sum_div]
      _ ≤ 1 * 1 := mul_le_mul hηsq ((div_le_one (hDpos x)).2 hAD)
        (div_nonneg (hAn x) (hDpos x).le) (by norm_num)
      _ = 1 := by ring
  refine ⟨s, χ, hχs, hχn, hχo, ?_, ?_, hχsum, ?_⟩
  · intro x hx
    have hηx : ∀ᶠ y in 𝓝 x, η y = 1 := hηone.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hηx, isOpen_interior.mem_nhds (hKL hx)] with y hηy hyL
    have hPy : P y = 1 := hpone y (interior_subset hyL)
    have hDy : D y = A y := by
      dsimp only [D]
      rw [hPy]
      ring
    simp only [χ, hηy, one_mul, div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt (hDpos y).le]
    change A y / D y = 1
    rw [← hDy]
    exact div_self (ne_of_gt (hDpos y))
  · intro i x
    have hsq : χ i x ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (χ j x)) (Finset.mem_univ i)).trans (hχsum x)
    exact (sq_le_one_iff₀ (hχn i x)).1 hsq
  · intro i
    have hηchart : tsupport (χ i) ⊆ (extChartAt (ComplexModel n) (i : M.Carrier)).source :=
      (hχo i).trans Set.inter_subset_left
    obtain ⟨hcψ, hψ, _⟩ := L18Aux.chartPullbackZero_smoothFn
      (i : M.Carrier) (hχs i).1 (hχs i).2 hηchart
    refine ⟨hψ, hcψ, ?_⟩
    intro z hz
    rcases L18Aux.chartPullbackZero_tsupport_subset (i : M.Carrier)
      (hχs i).2 hηchart hz with ⟨x, hx, rfl⟩
    refine ⟨(extChartAt (ComplexModel n) (i : M.Carrier)).map_source ((hχo i) hx).1, ?_⟩
    change chartInv (i : M.Carrier) (chartPt (i : M.Carrier) x) ∈
      (localTriv (r := r) E (i : M.Carrier)).baseSet
    rw [chartInv_chartPt_of_mem (i : M.Carrier) x
      (by simpa only [extChartAt_source] using ((hχo i) hx).1)]
    exact ((hχo i) hx).2

end Yau.LeafProofs.L14Aux
