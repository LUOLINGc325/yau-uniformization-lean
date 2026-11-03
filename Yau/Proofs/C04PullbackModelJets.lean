import Yau.Proofs.C04PullbackModelJetsAlpha
import Yau.Proofs.C04PullbackModelJetsComposition
import Yau.Proofs.C04NormalEllipticModelCalculus

/-! Uniform all-order bounds for the actual pullback Gram model of the same
rescaled inverse. The larger smooth domain and smaller bound domain are fixed. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_pullback_model_jet_bounds
    (R d : ℝ) (hR : 0 < R) (hd : 0 < d) (hd1 : d ≤ 1) (hdR : d ≤ R / 4)
    (B P : ℕ → ℝ) (hB : ∀ m, 0 < B m) (hP : ∀ m, 0 < P m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (A : E → E →L[ℝ] E) (ψ : E → E) (L : E →L[ℝ] E),
        ContDiff ℝ ∞ A →
        (∀ m x, x ∈ Metric.ball (0 : E) R → ‖iteratedFDeriv ℝ m A x‖ ≤ B m) →
        ContDiffOn ℝ ∞ ψ (Metric.ball (0 : E) (1 / 8 : ℝ)) →
        (∀ m w, w ∈ Metric.ball (0 : E) (1 / 8 : ℝ) → ‖iteratedFDeriv ℝ m ψ w‖ ≤ P m) →
        (∀ w ∈ Metric.ball (0 : E) (1 / 8 : ℝ), ‖ψ w‖ ≤ (4 / 3 : ℝ) * ‖w‖) →
        ‖L‖ ≤ (5 / 4 : ℝ) →
        ContDiffOn ℝ ∞ (pullbackModelMetric d A ψ L) (Metric.ball (0 : E) (d / 16)) ∧
          ∀ m z, z ∈ Metric.ball (0 : E) (d / 32) →
            ‖iteratedFDeriv ℝ m (pullbackModelMetric d A ψ L) z‖ ≤ C m := by
  let PA : ℕ → ℝ := pullbackModelParameterJetBudget d P
  have hPA (m : ℕ) : 0 < PA m := pullbackModelParameterJetBudget_pos d hd P hP m
  let PF : ℕ → ℝ := pullbackModelCompositionJetBudget PA B
  have hPF (m : ℕ) : 0 < PF m :=
    pullbackModelCompositionJetBudget_pos PA B (fun j => (hPA j).le) (fun j => (hB j).le) m
  let S : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * PF i * PA (m - i + 1)
  have hS (m : ℕ) : 0 ≤ S m := Finset.sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPF i).le) (hPA _).le
  let PQ : ℕ → ℝ := fun m => 1 + S m
  have hPQ (m : ℕ) : 0 < PQ m := by dsimp [PQ]; linarith [hS m]
  let T : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * PQ i * PQ (m - i)
  have hT (m : ℕ) : 0 ≤ T m := Finset.sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPQ i).le) (hPQ _).le
  refine ⟨fun m => 1 + 2 * T m, fun m => by linarith [hT m], ?_⟩
  intro A ψ L hA hAjet hψ hψjet hψnorm hL
  let U := Metric.ball (0 : E) (d / 16)
  let alpha := pullbackModelParameter d ψ L
  let F : E → E →L[ℝ] E := fun z => A (alpha z)
  let Q : E → E →L[ℝ] E := fun z => (F z).comp (fderiv ℝ alpha z)
  have halpha : ContDiffOn ℝ ∞ alpha U := pullback_model_parameter_smooth d hd ψ L hL hψ
  have hmap : Set.MapsTo alpha U (Metric.ball (0 : E) R) :=
    fun z hz => pullback_model_parameter_mem_ball R d hR hd hdR ψ L hL hψnorm hz
  have hF : ContDiffOn ℝ ∞ F U := hA.comp_contDiffOn halpha
  have hDA : ContDiffOn ℝ ∞ (fderiv ℝ alpha) U :=
    halpha.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have hQ : ContDiffOn ℝ ∞ Q U := hF.clm_comp hDA
  have hAlphaBound (m : ℕ) (z : E) (hz : z ∈ U) :
      ‖iteratedFDeriv ℝ m alpha z‖ ≤ PA m :=
    pullback_model_parameter_jet_bound d hd P hP ψ L hL hψ hψjet m hz
  have hFBound (m : ℕ) (z : E) (hz : z ∈ U) : ‖iteratedFDeriv ℝ m F z‖ ≤ PF m :=
    pullback_model_composition_jet halpha hA.contDiffOn Metric.isOpen_ball Metric.isOpen_ball
      hmap hz PA B (fun j => (hPA j).le) (fun j => (hB j).le)
      (fun j => hAlphaBound j z hz) (fun j => hAjet j (alpha z) (hmap hz)) m
  have hDABound (m : ℕ) (z : E) (hz : z ∈ U) :
      ‖iteratedFDeriv ℝ m (fderiv ℝ alpha) z‖ ≤ PA (m + 1) := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hAlphaBound (m + 1) z hz
  have hQBound (m : ℕ) (z : E) (hz : z ∈ U) : ‖iteratedFDeriv ℝ m Q z‖ ≤ PQ m := by
    have hh := normal_elliptic_bilinear_jet (ContinuousLinearMap.compL ℝ E E E)
      hF hDA Metric.isOpen_ball hz PF (fun j => PA (j + 1)) (fun j => (hPF j).le)
      (fun j => hFBound j z hz) (fun j => hDABound j z hz) m
    exact (hh.trans (mul_le_of_le_one_left (hS m) (ContinuousLinearMap.norm_compL_le ℝ E E E))).trans
      (by dsimp [PQ]; linarith)
  have hH : pullbackModelMetric d A ψ L = fun z => normalModelMetric (Q z) := by
    funext z
    exact pullbackModelMetric_eq_coframe d A ψ L z
  rw [hH]
  refine ⟨((normalModelGramBilinear (E := E)).contDiff.comp_contDiffOn hQ).clm_apply hQ, ?_⟩
  intro m z hz
  have hzU : z ∈ U := Metric.ball_subset_ball (by linarith) hz
  have hh := normal_elliptic_bilinear_jet (normalModelGramBilinear (E := E)) hQ hQ
    Metric.isOpen_ball hzU PQ PQ (fun j => (hPQ j).le)
    (fun j => hQBound j z hzU) (fun j => hQBound j z hzU) m
  exact (hh.trans (mul_le_mul_of_nonneg_right normalModelGramBilinear_norm (hT m))).trans
    (by linarith)

end Yau.Proofs.C04Aux
