import Yau.Proofs.F04SeeleyTermDerivatives

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem negativeJetTerm_uniform_bound {O K : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O) (hδ : 0 < δ) (hδS : δ < S)
    (hχ : ContDiff ℝ ∞ χ) (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ k p, p ∈ K ×ˢ Iic (0 : ℝ) →
      ‖negativeJetTerm O χ f m k p‖ ≤ (|seeleyWeight k| * dyadic k ^ m) * M := by
  obtain ⟨M, hM1, hM⟩ := positiveCutoff_jet_bound hO hK hKO hδ hδS hχ hχzero hf m
  refine ⟨M, hM1, ?_⟩
  intro k p hp
  apply negativeJetTerm_norm_le
  have ht : 0 ≤ -dyadic k * p.2 :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (dyadic_pos k).le) hp.2
  have he := hM p.1 hp.1 (-dyadic k * p.2) ht
  simpa only [reflectLinear_apply] using he

theorem negativeJet_hasFDerivAt {O W : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : closure W ⊆ O)
    (hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (m : ℕ) (p : E × ℝ)
    (hp : p ∈ W ×ˢ Iio 0) :
    HasFDerivAt (negativeJet O χ f m) (negativeJet O χ f (m + 1) p).curryLeft p := by
  obtain ⟨M, _hM, hM⟩ := negativeJetTerm_uniform_bound hO hWc hWO hδ hδS hχ hχzero hf m
  obtain ⟨D, _hD, hD⟩ := negativeJetTerm_uniform_bound hO hWc hWO hδ hδS hχ hχzero hf (m + 1)
  have hpclosed : p ∈ closure W ×ˢ Iic (0 : ℝ) :=
    ⟨subset_closure hp.1, (show p.2 < (0 : ℝ) from hp.2).le⟩
  have hs0 : Summable (fun k => negativeJetTerm O χ f m k p) :=
    ((seeleyWeight_summable m).mul_right M).of_norm_bounded (fun k => hM k p hpclosed)
  have hs1 : Summable (fun k => negativeJetTerm O χ f (m + 1) k p) :=
    ((seeleyWeight_summable (m + 1)).mul_right D).of_norm_bounded (fun k => hD k p hpclosed)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((hW.prod isOpen_Iio).mem_nhds hp)
  have hder : ∀ k q, q ∈ Metric.ball p r →
      HasFDerivAt (negativeJetTerm O χ f m k)
        (negativeJetTerm O χ f (m + 1) k q).curryLeft q := by
    intro k q hq
    exact negativeJetTerm_hasFDerivAt hO hδ hδS hχ hχzero hf m k q
      ⟨hWO (subset_closure (hball hq).1), (hball hq).2⟩
  have hnorm : ∀ k q, q ∈ Metric.ball p r →
      ‖(negativeJetTerm O χ f (m + 1) k q).curryLeft‖ ≤
        (|seeleyWeight k| * dyadic k ^ (m + 1)) * D := by
    intro k q hq
    rw [ContinuousMultilinearMap.curryLeft_norm]
    exact hD k q ⟨subset_closure (hball hq).1, (show q.2 < (0 : ℝ) from (hball hq).2).le⟩
  have ht := hasFDerivAt_tsum_of_isPreconnected
    ((seeleyWeight_summable (m + 1)).mul_right D) Metric.isOpen_ball
    (convex_ball p r).isPreconnected hder hnorm (Metric.mem_ball_self hr) hs0 (Metric.mem_ball_self hr)
  have heq : (negativeJet O χ f (m + 1) p).curryLeft =
      ∑' k, (negativeJetTerm O χ f (m + 1) k p).curryLeft := by
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E × ℝ) F).toContinuousLinearEquiv.toContinuousLinearMap.map_tsum hs1
  change HasFDerivAt (fun q => ∑' k, negativeJetTerm O χ f m k q)
    (negativeJet O χ f (m + 1) p).curryLeft p
  simpa only [← heq] using ht

end Yau.F04Proof.Seeley
