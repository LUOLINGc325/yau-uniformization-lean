import Yau.Proofs.F04SeeleyNegativeDerivatives

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous interior derivatives on an open spatial cylinder determine the genuine
derivative at its closed time face. -/
theorem halfTime_hasFDerivWithinAt {W : Set E} (hW : IsOpen W)
    {f : E × ℝ → F} {A : E × ℝ → (E × ℝ →L[ℝ] F)}
    (hf : ContinuousOn f (W ×ˢ Iic 0)) (hA : ContinuousOn A (W ×ˢ Iic 0))
    (hd : ∀ p ∈ W ×ˢ Iio 0, HasFDerivAt f (A p) p)
    (p : E × ℝ) (hp : p ∈ W ×ˢ Iic 0) :
    HasFDerivWithinAt f (A p) (W ×ˢ Iic 0) p := by
  obtain ⟨r, hr, hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hp.1)
  let U : Set (E × ℝ) := Metric.ball p.1 r ×ˢ Iio 0
  have hU : U ⊆ W ×ˢ Iio 0 := fun q hq => ⟨hrW (Metric.ball_subset_closedBall hq.1), hq.2⟩
  have hUc : closure U ⊆ W ×ˢ Iic 0 := by
    rw [show closure U = closure (Metric.ball p.1 r) ×ˢ Iic (0 : ℝ) by
      simp only [U, closure_prod_eq, closure_Iio]]
    exact fun q hq => ⟨hrW ((closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall) hq.1), hq.2⟩
  have hsub : U ⊆ W ×ˢ Iic 0 := fun q hq =>
    ⟨(hU hq).1, (show q.2 < (0 : ℝ) from hq.2).le⟩
  have hdU : ∀ q ∈ U, HasFDerivAt f (A q) q := fun q hq => hd q (hU hq)
  have hboundary : HasFDerivWithinAt f (A p) (closure U) p := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun q hq => (hdU q hq).differentiableAt.differentiableWithinAt)
      ((convex_ball p.1 r).prod (convex_Iio 0)) (Metric.isOpen_ball.prod isOpen_Iio)
    · exact fun q hq => (hf q (hUc hq)).mono hsub
    · apply ((hA p hp).mono hsub).congr'
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hdU q hq).fderiv.symm
  apply hboundary.mono_of_mem_nhdsWithin
  have hn : {q : E × ℝ | q.1 ∈ Metric.ball p.1 r} ∈ 𝓝 p :=
    continuous_fst.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with q hq hqW
  rw [show closure U = closure (Metric.ball p.1 r) ×ˢ Iic (0 : ℝ) by
    simp only [U, closure_prod_eq, closure_Iio]]
  exact ⟨subset_closure hq, hqW.2⟩

variable [CompleteSpace F]

theorem negativeJet_hasFDerivWithinAt {O W : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : closure W ⊆ O)
    (hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (m : ℕ) (p : E × ℝ)
    (hp : p ∈ W ×ˢ Iic 0) :
    HasFDerivWithinAt (negativeJet O χ f m)
      (negativeJet O χ f (m + 1) p).curryLeft (W ×ˢ Iic 0) p := by
  apply halfTime_hasFDerivWithinAt hW
    (negativeJet_continuousOn hO hW hWc hWO hδ hδS hχ hχzero hf m)
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E × ℝ) F).continuous.comp_continuousOn
      (negativeJet_continuousOn hO hW hWc hWO hδ hδS hχ hχzero hf (m + 1)))
    (fun q hq => negativeJet_hasFDerivAt hO hW hWc hWO hδ hδS hχ hχzero hf m q hq) p hp

end Yau.F04Proof.Seeley
