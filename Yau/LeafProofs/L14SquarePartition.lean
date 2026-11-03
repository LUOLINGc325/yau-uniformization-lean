import Yau.LeafProofs.L14Transitions

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

theorem exists_finite_smooth_bundle_partition {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ s : Finset M.Carrier, ∃ p : s → M.Carrier → ℝ,
      (∀ i, SmoothFn (p i)) ∧ (∀ i x, 0 ≤ p i x) ∧
        (∀ i, tsupport (p i) ⊆ bundleChartSource (r := r) E (i : M.Carrier)) ∧
          (∀ x ∈ K, ∑ i, p i x = 1) := by
  classical
  letI := L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  have hself (x : M.Carrier) : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (bundleChartSource (r := r) E)
    (bundleChartSource_isOpen (r := r) E)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hself x⟩)
  have hcover : K ⊆ ⋃ i : s, bundleChartSource (r := r) E (i : M.Carrier) := by
    intro x hx
    rcases Set.mem_iUnion.mp (hs hx) with ⟨a, ha⟩
    rcases Set.mem_iUnion.mp ha with ⟨has, hax⟩
    exact Set.mem_iUnion.mpr ⟨⟨a, has⟩, hax⟩
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexVector n)) hK.isClosed
    (fun i : s => bundleChartSource (r := r) E (i : M.Carrier))
    (fun i => bundleChartSource_isOpen (r := r) E (i : M.Carrier)) hcover
  refine ⟨s, fun i => p i, ?_, p.nonneg, hp, ?_⟩
  · intro i
    exact L18Aux.smoothFn_of_contMDiff_real (p i).contMDiff
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hx

theorem exists_finite_smooth_bundle_square_partition (g : Yau.SmoothMetric M)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ s : Finset M.Carrier, ∃ χ : s → M.Carrier → ℝ,
      (∀ i, SmoothFn (χ i) ∧ HasCompactSupport (χ i)) ∧
        (∀ i x, 0 ≤ χ i x) ∧
        (∀ i, tsupport (χ i) ⊆ bundleChartSource (r := r) E (i : M.Carrier)) ∧
        (∀ x ∈ K, ∀ᶠ y in 𝓝 x, ∑ i, χ i y ^ 2 = 1) := by
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
  refine ⟨s, χ, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, hηc.mul_right⟩
    intro a
    exact (hηs a).mul ((hps i a).div ((hDs a).sqrt
      (fun z _ => ne_of_gt (hDpos (chartInv a z))))
        (fun z _ => Real.sqrt_ne_zero'.mpr (hDpos (chartInv a z))))
  · intro i x
    exact mul_nonneg (hηrange x).1 (div_nonneg (hpn i x) (Real.sqrt_nonneg _))
  · intro i
    apply (closure_mono (show Function.support (χ i) ⊆ Function.support (p i) from ?_)).trans (hpo i)
    intro x hx hpzero
    apply hx
    simp only [χ, hpzero, zero_div, mul_zero]
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

end Yau.LeafProofs.L14Aux
