import Yau.Proofs.P06PDETypeTraceInitial

/-! Positive-time joint smoothness gives every compact spatial initial jet
for the actual translated field. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.P06Aux.PDETypeTrace
open Yau Yau.Blueprint
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem contDiffOn_partial_fderiv {O : Set E} {S : Set ℝ}
    (hO : IsOpen O) (hS : IsOpen S) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ S)) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => fderiv ℝ (fun w => f (w, p.2)) p.1) (O ×ˢ S) := by
  intro p hp
  have hg : ContDiffAt ℝ ∞
      (fun q : (E × ℝ) × E => f (q.2, q.1.2)) (p, p.1) :=
    (hf.contDiffAt ((hO.prod hS).mem_nhds hp)).comp _
      (contDiffAt_snd.prodMk (contDiffAt_snd.comp _ contDiffAt_fst))
  exact (hg.fderiv contDiffAt_fst (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).contDiffWithinAt

 theorem contDiffOn_spatial_jets {O : Set E} {S : Set ℝ}
    (hO : IsOpen O) (hS : IsOpen S) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ S)) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => iteratedFDeriv ℝ j (fun w => f (w, p.2)) p.1)
      (O ×ˢ S) := by
  induction j with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hf
  | succ j ih =>
    simpa [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm.contDiff.comp_contDiffOn
        (contDiffOn_partial_fderiv hO hS ih)

 theorem compact_spatial_jets_time_shift {O : Set E} (hO : IsOpen O)
    {f : E × ℝ → F} (hf : ContDiffOn ℝ ∞ f (O ×ˢ Ioi 0))
    {s : ℝ} (hs : 0 < s) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ j (fun w => f (w, s + t) - f (w, s)) z‖ < ε := by
  let J : E × ℝ → (E [×j]→L[ℝ] F) :=
    fun p => iteratedFDeriv ℝ j (fun w => f (w, p.2)) p.1
  have hJ : ContinuousOn J (K ×ˢ Icc (s / 2) (s + 1)) :=
    (contDiffOn_spatial_jets hO isOpen_Ioi hf j).continuousOn.mono
      (fun p hp => ⟨hKO hp.1, by change 0 < p.2; have hps : s / 2 ≤ p.2 := hp.2.1; linarith⟩)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hJ) ε hε
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro t ht htτ z hz
  have hst : 0 < s + t := add_pos hs ht
  have hf₁ : ContDiffAt ℝ j (fun w => f (w, s + t)) z :=
    (((hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun w hw => ⟨hw, hst⟩)).contDiffAt
      (hO.mem_nhds (hKO hz))).of_le (by simp))
  have hf₀ : ContDiffAt ℝ j (fun w => f (w, s)) z :=
    (((hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun w hw => ⟨hw, hs⟩)).contDiffAt
      (hO.mem_nhds (hKO hz))).of_le (by simp))
  rw [fun_iteratedFDeriv_sub_apply hf₁ hf₀, ← dist_eq_norm]
  apply hd (z, s + t) ⟨hz, by constructor <;> linarith [lt_of_lt_of_le htτ (min_le_right δ 1)]⟩
    (z, s) ⟨hz, by constructor <;> linarith⟩
  simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos ht] using
    (And.intro hδ (lt_of_lt_of_le htτ (min_le_left δ 1)))

 theorem formSmoothInitial_time_shift {n k : ℕ} {M : ComplexManifold n}
    {U : ℝ → RealForm M k} (hU : SmoothFormTime U (Ioi 0))
    {s : ℝ} (hs : 0 < s) : FormSmoothInitial (fun t => U (s + t)) (U s) := by
  refine ⟨by simp, ?_⟩
  intro x K hK hKO j I ε hε
  exact compact_spatial_jets_time_shift (isOpen_extChartAt_target (I := ComplexModel n) x)
    (hU x I) hs K hK hKO j ε hε

end Yau.NodeProofs.P06Aux.PDETypeTrace
