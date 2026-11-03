import Yau.Proofs.F04ZeroPastSmooth

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic

theorem iteratedFDeriv_eq_of_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {p : E} (he : f =ᶠ[𝓝 p] g) (m : ℕ) :
    iteratedFDeriv ℝ m f p = iteratedFDeriv ℝ m g p := by
  have hw : f =ᶠ[𝓝[univ] p] g := he.filter_mono nhdsWithin_le_nhds
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq he.eq_of_nhds m

theorem zeroPast_iteratedFDeriv_of_neg {n : ℕ} (u : Point n → ℝ)
    (m : ℕ) (p : Point n) (hp : p.2 < 0) : iteratedFDeriv ℝ m (zeroPast u) p = 0 := by
  have he : zeroPast u =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hp] with q hq
    exact zeroPast_of_nonpos u hq.le
  rw [iteratedFDeriv_eq_of_germ he m]
  have h0 : (fun _ : Point n => (0 : ℝ)) = (0 : Point n → ℝ) := by
    funext q
    rfl
  rw [h0]
  simpa only [iteratedFDerivWithin_univ, Pi.zero_apply] using congrFun
    (iteratedFDerivWithin_zero (𝕜 := ℝ) (E := Point n) (F := ℝ) (s := univ) (i := m)) p

theorem zeroPast_initial_iteratedFDeriv {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {s : ℝ} (hs : 0 < s) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ (zeroPast u) (O ×ˢ Ioo (-s) s))
    (x : Space n) (hx : x ∈ O) (m : ℕ) :
    iteratedFDeriv ℝ m (zeroPast u) (x, 0) = 0 := by
  have hp : (x, (0 : ℝ)) ∈ O ×ˢ Ioo (-s) s := ⟨hx, by linarith, hs⟩
  have hc := ((hu.contDiffAt ((hO.prod isOpen_Ioo).mem_nhds hp)).differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).continuousAt
  have hq : Tendsto (fun j : ℕ => (x, -(1 / ((j : ℝ) + 1)))) atTop (𝓝 (x, (0 : ℝ))) := by
    simpa only [neg_zero] using tendsto_const_nhds.prodMk_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hz : (fun j : ℕ => iteratedFDeriv ℝ m (zeroPast u) (x, -(1 / ((j : ℝ) + 1)))) =ᶠ[atTop]
      (fun _ => 0) := Eventually.of_forall (fun j => zeroPast_iteratedFDeriv_of_neg u m _ (by
        change -(1 / ((j : ℝ) + 1)) < 0
        exact neg_neg_of_pos (by positivity)))
  have hj := Filter.Tendsto.comp hc hq
  exact tendsto_nhds_unique hj (tendsto_const_nhds.congr' hz.symm)

/-- Every joint tensor jet of the original positive-time function tends to
 zero uniformly on each spatial compact set. -/
theorem zeroPast_uniform_compact_initial_jets {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {s : ℝ} (hs : 0 < s) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ (zeroPast u) (O ×ˢ Ioo (-s) s))
    (K : Set (Space n)) (hK : IsCompact K) (hKO : K ⊆ O) (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < s ∧ ∀ t ∈ Ioo 0 δ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m u (x, t)‖ < η := by
  let J := iteratedFDeriv ℝ m (zeroPast u)
  have hJC : ContinuousOn J (O ×ˢ Ioo (-s) s) := by
    intro p hp
    exact ((hu.contDiffAt ((hO.prod isOpen_Ioo).mem_nhds hp)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).continuousAt.continuousWithinAt
  have hKC : IsCompact (K ×ˢ Icc (0 : ℝ) (s / 2)) := hK.prod isCompact_Icc
  have hC : ContinuousOn J (K ×ˢ Icc (0 : ℝ) (s / 2)) := hJC.mono (by
    intro p hp
    exact ⟨hKO hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩)
  obtain ⟨d, hd, hDist⟩ := Metric.uniformContinuousOn_iff.mp
    (hKC.uniformContinuousOn_of_continuous hC) η hη
  refine ⟨min (s / 2) d, lt_min (half_pos hs) hd, (min_le_left _ _).trans_lt (half_lt_self hs), ?_⟩
  intro t ht x hx
  have htHalf : t ≤ s / 2 := ht.2.le.trans (min_le_left _ _)
  have htD : t < d := ht.2.trans_le (min_le_right _ _)
  have hDistPt : dist (x, t) (x, (0 : ℝ)) < d := by
    simpa only [Prod.dist_eq, dist_self, dist_zero_right, Real.norm_eq_abs,
      abs_of_pos ht.1, max_eq_right ht.1.le] using htD
  have hh := hDist (x, t) ⟨hx, ht.1.le, htHalf⟩ (x, 0) ⟨hx, le_rfl, (half_pos hs).le⟩ hDistPt
  have hJ0 : J (x, 0) = 0 := zeroPast_initial_iteratedFDeriv hO hs hu x (hKO hx) m
  have he : zeroPast u =ᶠ[𝓝 (x, t)] u := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds ht.1] with p hp
    exact zeroPast_of_pos u hp
  have hJ : J (x, t) = iteratedFDeriv ℝ m u (x, t) := iteratedFDeriv_eq_of_germ he m
  simpa only [hJ0, hJ, dist_zero_right] using hh

end Yau.F04Proof
