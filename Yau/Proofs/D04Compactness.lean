import Yau.Proofs.D04Mollifier
import Yau.Proofs.D04CompactnessTools

open MeasureTheory Filter
open scoped Topology ContDiff Convolution BoundedContinuousFunction

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {d : ℕ}

/-! Actual local L¹ compactness in arbitrary complex dimension. The input
is an original psh sequence with the same finite-a.e. local real class;
uniform radial approximation and Arzelà–Ascoli construct the subsequence. -/

/-- The local L¹ smoothing estimate for the original extended-real
potential, after a compact truncation outside the kernel neighborhoods. -/
theorem psh_radial_L1_error {O S K : Set (ComplexVector d)} {u : (ComplexVector d) → EReal}
    (hu : IsPshOn u O) (hL1 : CoordinateLocallyL1 O u)
    (hS : IsCompact S) (hSO : S ⊆ O) (hK : MeasurableSet K)
    {χ : (ComplexVector d) → ℝ} {C : NNReal} (hχ : LipschitzWith C χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z ∈ K, 1 ≤ χ z) {t : ℝ} (ht : 0 < t)
    (hballs : ∀ z ∈ Function.support χ, Metric.closedBall z (2 * t) ⊆ S) :
    (∫ z in K, |(∫ w, radialKernel t (z - w) *
      S.indicator (fun w ↦ (u w).toReal) w) - (u z).toReal|) ≤
      ((C : ℝ) * (2 * t)) * ∫ w in S, |(u w).toReal| := by
  let g : (ComplexVector d) → ℝ := S.indicator (fun w ↦ (u w).toReal)
  have hgi : Integrable g volume := (integrable_indicator_iff hS.measurableSet).mpr (hL1 S hS hSO).2
  have hfin : ∀ᵐ z ∂volume, z ∈ S → u z ≠ ⊥ ∧ u z ≠ ⊤ :=
    (ae_restrict_iff' hS.measurableSet).mp (hL1 S hS hSO).1
  have hmajor : ∀ᵐ z ∂volume, z ∈ Function.support χ →
      g z ≤ ∫ w, radialKernel t (z - w) * g w := by
    filter_upwards [hfin] with z hz
    intro hzχ
    have hball := hballs z hzχ
    have hzS := hball (Metric.mem_closedBall_self (by positivity : 0 ≤ 2 * t))
    obtain ⟨hzbot, hztop⟩ := hz hzS
    have h := psh_le_radialConvolution hu hL1 ht (hball.trans hSO)
    apply EReal.coe_le_coe_iff.mp
    change ((S.indicator (fun w ↦ (u w).toReal) z : ℝ) : EReal) ≤ _
    rw [Set.indicator_of_mem hzS, EReal.coe_toReal hztop hzbot,
      radialConvolution_indicator_eq ht (fun w ↦ (u w).toReal) hball]
    exact h
  have hKS : K ⊆ S := by
    intro z hz
    have hzχ : z ∈ Function.support χ :=
      ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (hχ1 z hz))
    exact hballs z hzχ (Metric.mem_closedBall_self (by positivity : 0 ≤ 2 * t))
  have herr := radialConvolution_L1_error_on ht hgi hχ hsχ hχ0 hK hχ1 hmajor
  have hleft : (∫ z in K, |(∫ w, radialKernel t (z - w) * g w) - g z|) =
      ∫ z in K, |(∫ w, radialKernel t (z - w) * g w) - (u z).toReal| := by
    apply setIntegral_congr_fun hK
    intro z hz
    change |(∫ w, radialKernel t (z - w) * g w) - S.indicator (fun w ↦ (u w).toReal) z| = _
    rw [Set.indicator_of_mem (hKS hz)]
  have hright : (∫ w, |g w|) = ∫ w in S, |(u w).toReal| := by
    rw [← integral_indicator hS.measurableSet]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ S
    · simp only [g, Set.indicator_of_mem hw]
    · simp only [g, Set.indicator_of_notMem hw, abs_zero]
  rw [hleft, hright] at herr
  exact herr

theorem exists_smooth_compact_majorant {O K : Set (ComplexVector d)} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ χ : (ComplexVector d) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z ∈ K, χ z = 1) := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨χ, hχ, hχrange, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) Metric.isOpen_thickening hK.isClosed
      (Metric.self_subset_thickening hδ K)
  have hsupp : tsupport χ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hχsupp]
    exact Metric.closure_thickening_subset_cthickening δ K
  have hcompact : HasCompactSupport χ :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) hsupp
  exact ⟨χ, hχ, hcompact, hsupp.trans hδO,
    fun z ↦ (hχrange (Set.mem_range_self z)).1, fun z hz ↦ (hχone z).mp hz⟩

/-- The exact compactness assumptions give one compact truncation and a
uniform local L¹ smoothing error tending to zero with the radius. -/
theorem uniform_radial_L1_approx {O : Set (ComplexVector d)} {u : ℕ → (ComplexVector d) → EReal}
    (hO : IsOpen O) (hu : ∀ j, IsPshOn (u j) O ∧
      CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {K : Set (ComplexVector d)} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ (S : Set (ComplexVector d)) (T M : ℝ), IsCompact S ∧ S ⊆ O ∧ K ⊆ S ∧ 0 < T ∧ 0 ≤ M ∧
      (∀ j, Integrable (S.indicator (fun w ↦ (u j w).toReal)) volume) ∧
      ∀ j t, 0 < t → t ≤ T →
        (∫ z in K, |(∫ w, radialKernel t (z - w) *
          S.indicator (fun w ↦ (u j w).toReal) w) - (u j z).toReal|) ≤ M * t := by
  obtain ⟨χ, hχ, hsχ, hsχO, hχ0, hχ1⟩ := exists_smooth_compact_majorant hO hK hKO
  obtain ⟨C, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsχ hχ (by simp)
  obtain ⟨η, hη, hηO⟩ := hsχ.exists_cthickening_subset_open hO hsχO
  let S := Metric.cthickening η (tsupport χ)
  have hS : IsCompact S := hsχ.cthickening
  have hKS : K ⊆ S := by
    intro z hz
    apply Metric.self_subset_cthickening (tsupport χ)
    apply subset_tsupport χ
    change χ z ≠ 0
    rw [hχ1 z hz]
    norm_num
  obtain ⟨B, hB⟩ := hbound S hS hηO
  refine ⟨S, η / 2, (C : ℝ) * 2 * max B 0, hS, hηO, hKS, half_pos hη, by positivity, ?_, ?_⟩
  · intro j
    exact (integrable_indicator_iff hS.measurableSet).mpr ((hu j).2 S hS hηO).2
  · intro j t ht htT
    have hballs : ∀ z ∈ Function.support χ, Metric.closedBall z (2 * t) ⊆ S := by
      intro z hz
      exact (Metric.closedBall_subset_closedBall (show 2 * t ≤ η by linarith)).trans
        (Metric.closedBall_subset_cthickening (subset_tsupport χ hz) η)
    have herr := psh_radial_L1_error (hu j).1 (hu j).2 hS hηO hK.measurableSet
      hLip hsχ hχ0 (fun z hz ↦ by rw [hχ1 z hz]) ht hballs
    apply herr.trans
    calc
      _ ≤ ((C : ℝ) * (2 * t)) * max B 0 :=
        mul_le_mul_of_nonneg_left ((hB j).trans (le_max_left _ _)) (by positivity)
      _ = _ := by ring


/-- Countably many local L¹ seminorms admit a common Cauchy subsequence,
using the concrete radial approximation and Arzelà–Ascoli results above. -/
theorem psh_L1Cauchy_subseq {O : Set (ComplexVector d)} {u : ℕ → (ComplexVector d) → EReal}
    (hO : IsOpen O) (hu : ∀ j, IsPshOn (u j) O ∧
      CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    (K : ℕ → Set (ComplexVector d)) (hK : ∀ m, IsCompact (K m)) (hKO : ∀ m, K m ⊆ O) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ m ε, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
        (∫ z in K m, |(u (σ i) z).toReal - (u (σ j) z).toReal|) < ε := by
  choose S T M hS hSO hKS hT hM hgi herr using
    (fun m ↦ uniform_radial_L1_approx hO hu hbound (hK m) (hKO m))
  let g : ℕ → ℕ → (ComplexVector d) → ℝ := fun m j ↦ (S m).indicator (fun z ↦ (u j z).toReal)
  have hgbound (m : ℕ) : ∃ B : ℝ, ∀ j, (∫ w, |g m j w|) ≤ B := by
    obtain ⟨B, hB⟩ := hbound (S m) (hS m) (hSO m)
    refine ⟨B, ?_⟩
    intro j
    rw [integral_abs_indicator _ (hS m).measurableSet]
    exact hB j
  choose B hB using hgbound
  let t : ℕ × ℕ → ℝ := fun p ↦ T p.1 / ((p.2 : ℝ) + 1)
  have ht (p : ℕ × ℕ) : 0 < t p := div_pos (hT p.1) (by positivity)
  have htT (p : ℕ × ℕ) : t p ≤ T p.1 := by
    apply (div_le_iff₀ (by positivity : 0 < (p.2 : ℝ) + 1)).mpr
    nlinarith [mul_nonneg (hT p.1).le (Nat.cast_nonneg p.2 : 0 ≤ (p.2 : ℝ))]
  let f : (ℕ × ℕ) → ℕ → (ComplexVector d) → ℝ := fun p j z ↦
    ∫ w, radialKernel (t p) (z - w) * g p.1 j w
  have hfbounds (p : ℕ × ℕ) : ∃ (A : ℝ) (C : NNReal), 0 ≤ A ∧
      (∀ j z, |f p j z| ≤ A) ∧ (∀ j, LipschitzWith C (f p j)) :=
    radialConvolution_uniform_bounds (ht p) (hgi p.1) (hB p.1)
  choose A C hA0 hA hLip using hfbounds
  obtain ⟨σ, hσ, hσC⟩ := uniformlyCauchy_subseq_countable (fun p : ℕ × ℕ ↦ K p.1)
    (fun p ↦ hK p.1) f A C (fun p j z _ ↦ hA p j z) hLip
  refine ⟨σ, hσ, ?_⟩
  intro m ε hε
  have hsmall : Tendsto (fun l : ℕ ↦ M m * t (m, l)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (Yau.LeafProofs.L08_tendsto_natScale (T m))
  obtain ⟨l, hl⟩ := ((tendsto_order.mp hsmall).2 (ε / 3) (by linarith)).exists
  let δ := ε / (3 * (volume.real (K m) + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := hσC (m, l) δ hδ
  refine ⟨N, ?_⟩
  intro i hi j hj
  have hierr : (∫ z in K m, |(u (σ i) z).toReal - f (m, l) (σ i) z|) ≤ M m * t (m, l) := by
    simpa only [abs_sub_comm] using herr m (σ i) (t (m, l)) (ht _) (htT _)
  have hjerr : (∫ z in K m, |f (m, l) (σ j) z - (u (σ j) z).toReal|) ≤ M m * t (m, l) :=
    herr m (σ j) (t (m, l)) (ht _) (htT _)
  have hmid : (∫ z in K m, |f (m, l) (σ i) z - f (m, l) (σ j) z|) ≤
      δ * volume.real (K m) := integral_abs_le_const (hK m) (fun z hz ↦ (hN i hi j hj z hz).le)
  have hmidε : δ * volume.real (K m) ≤ ε / 3 := by
    calc
      _ ≤ δ * (volume.real (K m) + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = _ := by
        dsimp only [δ]
        field_simp [ne_of_gt (show 0 < volume.real (K m) + 1 by positivity)]
  have htri := Yau.LeafProofs.L08_integral_abs_triangle3 ((hu (σ i)).2 (K m) (hK m) (hKO m)).2
    ((hu (σ j)).2 (K m) (hK m) (hKO m)).2
    ((integrable_radialConvolution (ht (m, l)) (hgi m (σ i))).mono_measure Measure.restrict_le_self)
    ((integrable_radialConvolution (ht (m, l)) (hgi m (σ j))).mono_measure Measure.restrict_le_self)
  change (∫ z in K m, |(u (σ i) z).toReal - (u (σ j) z).toReal|) ≤
    (∫ z in K m, |(u (σ i) z).toReal - f (m, l) (σ i) z|) +
      (∫ z in K m, |f (m, l) (σ i) z - f (m, l) (σ j) z|) +
      ∫ z in K m, |f (m, l) (σ j) z - (u (σ j) z).toReal| at htri
  linarith


theorem L1_convergence_mono_set {S T : Set (ComplexVector d)} (hST : S ⊆ T)
    {f : ℕ → (ComplexVector d) → ℝ} (hf : ∀ j, IntegrableOn (f j) T volume) {g : (ComplexVector d) → ℝ}
    (hg : IntegrableOn g T volume)
    (hconv : Tendsto (fun j ↦ ∫ z in T, |f j z - g z|) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ z in S, |f j z - g z|) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _) _ hconv
  intro j
  exact setIntegral_mono_set ((hf j).sub hg).norm (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
    (Filter.Eventually.of_forall hST)

/-- The compactness assumptions already yield a single real local L¹
limit. The subharmonic representative is constructed separately. -/
theorem psh_exists_real_L1_limit {O : Set (ComplexVector d)} {u : ℕ → (ComplexVector d) → EReal}
    (hO : IsOpen O) (hu : ∀ j, IsPshOn (u j) O ∧
      CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B) :
    ∃ (σ : ℕ → ℕ) (v : (ComplexVector d) → ℝ), StrictMono σ ∧
      (∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn v S volume) ∧
      ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
        Tendsto (fun j ↦ ∫ z in S, |(u (σ j) z).toReal - v z|) atTop (𝓝 0) := by
  classical
  obtain ⟨K, hK, hKO, hmono, hcover⟩ := exists_compact_exhaustion hO
  obtain ⟨σ, hσ, hCauchy⟩ := psh_L1Cauchy_subseq hO hu hbound K hK hKO
  have hloc (m : ℕ) : ∃ f : (ComplexVector d) → ℝ, IntegrableOn f (K m) volume ∧
      Tendsto (fun j ↦ ∫ z in K m, |(u (σ j) z).toReal - f z|) atTop (𝓝 0) :=
    Yau.LeafProofs.L08_exists_L1_limit (fun j z ↦ (u (σ j) z).toReal)
      (fun j ↦ ((hu (σ j)).2 (K m) (hK m) (hKO m)).2) (hCauchy m)
  choose f hf hconv using hloc
  have hcompat (n m : ℕ) (hnm : n ≤ m) : f n =ᵐ[volume.restrict (K n)] f m := by
    apply Yau.LeafProofs.L08_L1_limit_unique (fun j ↦ ((hu (σ j)).2 (K n) (hK n) (hKO n)).2)
      (hf n) ((hf m).mono_set (hmono hnm)) (hconv n)
    exact L1_convergence_mono_set (hmono hnm)
      (fun j ↦ ((hu (σ j)).2 (K m) (hK m) (hKO m)).2) (hf m) (hconv m)
  have hmem (z : (ComplexVector d)) (hz : z ∈ O) : ∃ n, z ∈ K n := by
    obtain ⟨n, hn⟩ := hcover {z} isCompact_singleton (Set.singleton_subset_iff.mpr hz)
    exact ⟨n, hn (Set.mem_singleton z)⟩
  let idx : O → ℕ := fun z ↦ Nat.find (hmem z z.2)
  let v : (ComplexVector d) → ℝ := fun z ↦ if hz : z ∈ O then f (idx ⟨z, hz⟩) z else 0
  have hveq (m : ℕ) : v =ᵐ[volume.restrict (K m)] f m := by
    have hall : ∀ᵐ z ∂volume, ∀ n : ℕ, n ≤ m → z ∈ K n → f n z = f m z := by
      apply ae_all_iff.mpr
      intro n
      by_cases hnm : n ≤ m
      · have hn := (ae_restrict_iff' (hK n).measurableSet).mp (hcompat n m hnm)
        exact hn.mono fun z hz _ ↦ hz
      · exact Filter.Eventually.of_forall fun _ hn ↦ (hnm hn).elim
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (hK m).measurableSet] with z hz hzK
    have hzO := hKO m hzK
    have hidx : idx ⟨z, hzO⟩ ≤ m := Nat.find_min' (hmem z hzO) hzK
    have hidxmem : z ∈ K (idx ⟨z, hzO⟩) := Nat.find_spec (hmem z hzO)
    change (if hz : z ∈ O then f (idx ⟨z, hz⟩) z else 0) = f m z
    rw [dite_eq_left hzO]
    exact hz _ hidx hidxmem
  have hvint (m : ℕ) : IntegrableOn v (K m) volume := (hf m).congr (hveq m).symm
  have hvconv (m : ℕ) :
      Tendsto (fun j ↦ ∫ z in K m, |(u (σ j) z).toReal - v z|) atTop (𝓝 0) := by
    apply (hconv m).congr'
    apply Filter.Eventually.of_forall
    intro j
    apply integral_congr_ae
    filter_upwards [hveq m] with z hz
    rw [hz]
  refine ⟨σ, v, hσ, ?_, ?_⟩
  · intro S hS hSO
    obtain ⟨m, hm⟩ := hcover S hS hSO
    exact (hvint m).mono_set hm
  · intro S hS hSO
    obtain ⟨m, hm⟩ := hcover S hS hSO
    exact L1_convergence_mono_set hm
      (fun j ↦ ((hu (σ j)).2 (K m) (hK m) (hKO m)).2) (hvint m) (hvconv m)

end Yau.Proofs.D04Aux
