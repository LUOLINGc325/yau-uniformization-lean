import Yau.Proofs.U02Clock
import Yau.Proofs.U02JetComparison
import Yau.Proofs.U02JetDecay
import Yau.Proofs.U02ModelJetBudget
import Yau.Proofs.V03HolomorphicSmooth

/-! The original geometric transitions and polynomial jet conjugacy give
the uniform local defect required by U01, on the same physical clock. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem models_raw_transition_regularity {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {R : ℝ} (hRr1 : R ≤ r1) :
    ∀ᶠ k in atTop,
      ContDiffOn ℂ ∞ (F (tk k) (tk (k + 1))) (ball 0 R) ∧
      ∀ z ∈ ball (0 : ComplexVector n) R, ‖F (tk k) (tk (k + 1)) z‖ ≤ Cb := by
  rcases hc with ⟨_, _, _, _, _, htransition, _⟩
  filter_upwards [eventually_models_time_ge hf hp ht t0] with k hk
  have hh := htransition (tk k) (tk (k + 1)) hk (hp.1.monotone (Nat.le_succ k))
  have hsubset : ball (0 : ComplexVector n) R ⊆ ball 0 r1 := ball_subset_ball hRr1
  exact ⟨V03Proof.complex_holomorphic_contDiffOn isOpen_ball (hh.1.mono hsubset),
    fun z hz => (hh.2.1 z (hsubset hz)).2⟩

theorem models_uniform_raw_defect {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {nu R : ℝ}
    (hnu : 0 < nu) (hd : 30 < ((d : ℝ) + 1) * nu)
    (hR : 0 < R) (hR1 : R ≤ 1) (hRr1 : R ≤ r1)
    (hdelta : Real.exp hm - 1 ≤ 1)
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ 1 / 8) :
    ∀ᶠ k in atTop, ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-5 * nu * rho o (tk k)) →
      ‖(H (k + 1)).eval (F (tk k) (tk (k + 1)) z) - (G k).eval ((H k).eval z)‖ ≤
        Real.exp (-10 * rho o (tk k)) := by
  let B := max 1 Cb
  have hB : 1 ≤ B := le_max_left _ _
  have hsmall : ∀ᶠ k in atTop, Real.exp (-5 * nu * rho o (tk k)) < R := by
    simpa only [neg_mul] using eventually_exp_decay_lt hp.2.1
      (by positivity : 0 < 5 * nu) hR
  filter_upwards [models_raw_transition_regularity hf hc hp ht hRr1,
    models_jet_budget hp hdelta hpaid hB,
    eventual_jet_decay hp.2.1 hR hd, hsmall] with k hk hbudget hdecay hraw
  intro z hz
  have hdeg : (H (k + 1)).degree ≤ Nat.ceil Dg :=
    degree_le_natCeil (hp.2.2.2.2.2.2.1 (k + 1)).1
  have hbound := polynomial_jet_conjugacy_bound (H (k + 1)) (G k) (H k)
    hR hR1 hB hdeg hk.1
    (fun w hw => (hk.2 w hw).trans (le_max_right 1 Cb))
    (hp.2.2.2.2.2.1 k) (hz.trans_lt hraw)
  calc
    _ ≤ ((H (k + 1)).coeffNorm * B ^ Nat.ceil Dg + ((G k).comp (H k)).coeffNorm) *
        (‖z‖ / R) ^ (d + 1) := hbound
    _ ≤ Real.exp (rho o (tk k)) * (‖z‖ / R) ^ (d + 1) :=
      mul_le_mul_of_nonneg_right hbudget (pow_nonneg (div_nonneg (norm_nonneg _) hR.le) _)
    _ ≤ _ := hdecay ‖z‖ (norm_nonneg _) hz

end Yau.NodeProofs.U02Proof
