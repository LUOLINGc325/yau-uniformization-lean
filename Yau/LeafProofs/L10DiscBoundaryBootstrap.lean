import Yau.LeafProofs.L10DiscBoundaryFrame

/-! Extending the computed Euler derivative through convex caps and
bootstrapping the angular/Euler system on the punctured closed disc. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discBoundaryPunctured : Set ℂ :=
  Metric.closedBall (0 : ℂ) 1 ∩ ({0} : Set ℂ)ᶜ

theorem discBoundaryPunctured_uniqueDiffOn : UniqueDiffOn ℝ discBoundaryPunctured :=
  disc_closedBall_uniqueDiffOn.inter isClosed_singleton.isOpen_compl

theorem discBoundary_hasFDerivWithinAt_of_interior
    {v : ℂ → ℂ} {B : ℂ → (ℂ →L[ℝ] ℂ)}
    (hv : ContinuousOn v discBoundaryPunctured) (hB : ContinuousOn B discBoundaryPunctured)
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → HasFDerivAt v (B z) z) :
    ∀ x ∈ discBoundaryPunctured, HasFDerivWithinAt v (B x) discBoundaryPunctured x := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa [discBoundaryPunctured] using hx.2
  let δ : ℝ := ‖x‖ / 2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr hx0)
  let Q := Metric.ball x δ
  let s := Q ∩ Metric.ball (0 : ℂ) 1
  have hcl : closure s ⊆ Metric.closedBall x δ ∩ Metric.closedBall (0 : ℂ) 1 := by
    apply (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).closure_subset_iff.mpr
    exact fun y hy => ⟨Metric.ball_subset_closedBall hy.1, Metric.ball_subset_closedBall hy.2⟩
  have hcls : closure s ⊆ discBoundaryPunctured := by
    intro y hy
    have hy' := hcl hy
    refine ⟨hy'.2, ?_⟩
    have hy0 : y ≠ 0 := by
      intro heq
      have hh : ‖x‖ ≤ ‖x‖ / 2 := by simpa [heq, δ] using hy'.1
      have hxpos := norm_pos_iff.mpr hx0
      linarith
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
  have hsS : s ⊆ discBoundaryPunctured := fun y hy => hcls (subset_closure hy)
  have hlim : Tendsto (fderiv ℝ v) (𝓝[s] x) (𝓝 (B x)) := by
    have ht : Tendsto B (𝓝[s] x) (𝓝 (B x)) := (hB x hx).mono hsS
    have heq : B =ᶠ[𝓝[s] x] fderiv ℝ v := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hd y hy.2 (by simpa [discBoundaryPunctured] using (hsS hy).2)).fderiv.symm
    exact Filter.Tendsto.congr' heq ht
  have hdiff : HasFDerivWithinAt v (B x) (closure s) x := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hd y hy.2 (by simpa [discBoundaryPunctured] using (hsS hy).2)).differentiableAt.differentiableWithinAt)
      ((convex_ball _ _).inter (convex_ball _ _))
      (Metric.isOpen_ball.inter Metric.isOpen_ball) _ hlim
    intro y hy
    exact (hv y (hcls hy)).mono hsS
  apply hdiff.mono_of_mem_nhdsWithin
  have hQ : Q ∈ 𝓝 x := Metric.ball_mem_nhds x hδ
  have hQS : Q ∩ discBoundaryPunctured ∈ 𝓝[discBoundaryPunctured] x :=
    inter_mem (mem_nhdsWithin_of_mem_nhds hQ) self_mem_nhdsWithin
  apply mem_of_superset hQS
  intro y hy
  apply Metric.isOpen_ball.inter_closure
  exact ⟨hy.1, (closure_ball (0 : ℂ) (r := 1) (by norm_num)).symm ▸ hy.2.1⟩

theorem discBoundary_contDiffOn_nat_succ {s : Set ℂ} (hs : UniqueDiffOn ℝ s) (n : ℕ)
    {g : ℂ → ℂ} {G : ℂ → (ℂ →L[ℝ] ℂ)}
    (hG : ContDiffOn ℝ n G s) (hg : ∀ z ∈ s, HasFDerivWithinAt g (G z) s z) :
    ContDiffOn ℝ (n + 1 : ℕ) g s := by
  have h := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := (n : ℕ∞ω)) hs).2 ⟨by simp, G, hG, hg⟩
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem discAngularBoundaryBootstrap : DiscAngularBoundaryBootstrapGap := by
  intro u f hf huInterior hPDE huOne
  let U : ℕ → ℂ → ℂ := fun k => discAngularIterate k u
  let V : ℕ → ℂ → ℂ := fun k => discBoundaryEuler (U k)
  let F : ℕ → ℂ → ℂ := fun k => discAngularIterate k f
  let A : ℕ → ℂ → (ℂ →L[ℝ] ℂ) := fun k z =>
    discBoundaryFrame z (V k z) (U (k + 1) z)
  let B : ℕ → ℂ → (ℂ →L[ℝ] ℂ) := fun k z =>
    discBoundaryFrame z (Complex.normSq z • F k z - U (k + 2) z) (V (k + 1) z)
  have hSnonzero : ∀ z ∈ discBoundaryPunctured, z ≠ 0 := by
    intro z hz
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz.2
  have hUcont : ∀ k, ContinuousOn (U k) discBoundaryPunctured :=
    fun k => (huOne k).continuousOn.mono Set.inter_subset_left
  have hVcont : ∀ k, ContinuousOn (V k) discBoundaryPunctured := by
    intro k
    exact (((huOne k).continuousOn_fderivWithin disc_closedBall_uniqueDiffOn (by norm_num)).clm_apply
      continuousOn_id).mono Set.inter_subset_left
  have hF : ∀ (n k : ℕ), ContDiffOn ℝ n (F k) discBoundaryPunctured := by
    intro n k
    exact ((discAngularIterate_contDiffOn hf k).of_le (by simp)).mono Set.inter_subset_left
  have hQ : ∀ n : ℕ, ContDiffOn ℝ n Complex.normSq discBoundaryPunctured := by
    intro n
    have hr : ContDiffOn ℝ n (fun z : ℂ => z.re) discBoundaryPunctured :=
      Complex.reCLM.contDiff.contDiffOn
    have hi : ContDiffOn ℝ n (fun z : ℂ => z.im) discBoundaryPunctured :=
      Complex.imCLM.contDiff.contDiffOn
    exact (hr.mul hr).add (hi.mul hi)
  have hDU : ∀ k z, z ∈ discBoundaryPunctured → HasFDerivWithinAt (U k) (A k z) discBoundaryPunctured z := by
    intro k z hz
    have hd := ((huOne k).differentiableOn (by norm_num) z hz.1).hasFDerivWithinAt
    have hframe : A k z = fderivWithin ℝ (U k) (Metric.closedBall (0 : ℂ) 1) z :=
      discBoundaryFrame_reconstruct _ (hSnonzero z hz)
    exact (hd.mono Set.inter_subset_left).congr_fderiv hframe.symm
  have hDV : ∀ k z, z ∈ discBoundaryPunctured → HasFDerivWithinAt (V k) (B k z) discBoundaryPunctured z := by
    intro k
    apply discBoundary_hasFDerivWithinAt_of_interior (hVcont k)
    · have hb0 : ContDiffOn ℝ 0 (B k) discBoundaryPunctured :=
        discBoundaryFrame_contDiffOn hSnonzero
          (((hQ 0).smul (hF 0 k)).sub (contDiffOn_zero.mpr (hUcont (k + 2))))
          (contDiffOn_zero.mpr (hVcont (k + 1)))
      exact hb0.continuousOn
    · intro z hz hz0
      have hg : ContDiffAt ℝ 2 (U k) z :=
        ((huInterior k).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)
      have hd := discBoundaryEuler_hasFDerivAt hz hz0 hg
      change HasFDerivAt (discBoundaryEuler (U k))
        (discBoundaryFrame z (Complex.normSq z • F k z - U (k + 2) z) (V (k + 1) z)) z
      rw [show F k z = LeafCandidates.planarLaplacian (U k) z from (hPDE k z hz).symm]
      exact hd
  have hboot : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ n (U k) discBoundaryPunctured ∧ ContDiffOn ℝ n (V k) discBoundaryPunctured := by
    intro n
    induction n with
    | zero =>
        intro k
        exact ⟨contDiffOn_zero.mpr (hUcont k), contDiffOn_zero.mpr (hVcont k)⟩
    | succ n ih =>
        intro k
        have hA : ContDiffOn ℝ n (A k) discBoundaryPunctured :=
          discBoundaryFrame_contDiffOn hSnonzero (ih k).2 (ih (k + 1)).1
        have hB : ContDiffOn ℝ n (B k) discBoundaryPunctured :=
          discBoundaryFrame_contDiffOn hSnonzero
            (((hQ n).smul (hF n k)).sub (ih (k + 2)).1) (ih (k + 1)).2
        exact ⟨discBoundary_contDiffOn_nat_succ discBoundaryPunctured_uniqueDiffOn n hA (hDU k),
          discBoundary_contDiffOn_nat_succ discBoundaryPunctured_uniqueDiffOn n hB (hDV k)⟩
  have huS : ContDiffOn ℝ ∞ u discBoundaryPunctured := by
    apply contDiffOn_infty.mpr
    intro n
    exact (hboot n 0).1
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have hu0 : ContDiffOn ℝ ∞ u (Metric.ball (0 : ℂ) 1) := huInterior 0
    exact (hu0.contDiffAt (Metric.isOpen_ball.mem_nhds (by simp))).contDiffWithinAt
  · have hzS : z ∈ discBoundaryPunctured := ⟨hz, by simpa using hz0⟩
    apply (huS z hzS).mono_of_mem_nhdsWithin
    exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hz0)))

theorem discGreenSolution_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discGreenSolution f) (Metric.closedBall (0 : ℂ) 1) :=
  discGreenSolution_contDiffOn_of_angularBootstrap discAngularBoundaryBootstrap hf

theorem discGreenSolution_hasFTaylorSeries {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    HasFTaylorSeriesUpToOn ∞ (discGreenSolution f)
      (ftaylorSeriesWithin ℝ (discGreenSolution f) (Metric.closedBall (0 : ℂ) 1))
      (Metric.closedBall (0 : ℂ) 1) :=
  (discGreenSolution_contDiffOn hf).ftaylorSeriesWithin disc_closedBall_uniqueDiffOn

theorem discGreen_smoothDirichlet {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, LeafCandidates.planarLaplacian u z = f z) := by
  exact ⟨discGreenSolution f, discGreenSolution_contDiffOn hf,
    fun z hz => discGreenSolution_boundary f hz, fun z hz => discGreenSolution_laplacian hf hz⟩

end Yau.LeafProofs
