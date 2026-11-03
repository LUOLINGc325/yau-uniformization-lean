import Yau.Proofs.U02TransitionContinuation
import Yau.Proofs.U02ModelDefect
import Yau.Proofs.U02SmallPolynomials

/-! Regime (ii) gives a corrected orbit uniformly for every late starting
sheet. The cocycle is proved on that whole closed ball before substitution. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem regime_two_corrected_orbit {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {nu gamma lambda Tgamma R : ℝ}
    (hnu : 0 < nu) (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hmargin : 5 * nu ≤ lambda) (hd : 30 < ((d : ℝ) + 1) * nu)
    (hR : 0 < R) (hR1 : R ≤ 1) (hRr1 : R ≤ r1)
    (hdelta : Real.exp hm - 1 ≤ 1) (hpaid : |Cd| * (Real.exp hm - 1) ≤ 1 / 8)
    (hregime : ∀ t t', Tgamma ≤ t → t ≤ t' → ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-gamma * rho o t) → ‖F t t' z‖ ≤ Real.exp (-lambda * rho o t')) :
    ∀ᶠ a in atTop, ∀ j, a ≤ j → ∀ z ∈ closedBall (0 : ComplexVector n)
      (Real.exp (-gamma * rho o (tk a))),
      ‖(H j).eval (F (tk a) (tk j) z)‖ ≤ Real.exp (-2 * nu * rho o (tk j)) ∧
      ‖(H (j + 1)).eval (F (tk a) (tk (j + 1)) z) -
        (G j).eval ((H j).eval (F (tk a) (tk j) z))‖ ≤ Real.exp (-10 * rho o (tk j)) := by
  have hall : ∀ᶠ k in atTop,
      (∀ w : ComplexVector n, ‖w‖ ≤ Real.exp (-lambda * rho o (tk k)) →
        ‖(H k).eval w‖ ≤ Real.exp (-(2 * nu) * rho o (tk k))) ∧
      (∀ w : ComplexVector n, ‖w‖ ≤ Real.exp (-5 * nu * rho o (tk k)) →
        ‖(H (k + 1)).eval (F (tk k) (tk (k + 1)) w) - (G k).eval ((H k).eval w)‖ ≤
          Real.exp (-10 * rho o (tk k))) ∧
      Real.exp (-lambda * rho o (tk k)) < r1 ∧
      Real.exp (-gamma * rho o (tk k)) < r1 ∧
      max t0 Tgamma ≤ tk k ∧ 0 ≤ rho o (tk k) := by
    filter_upwards [model_H_small_ball hp hlambda (by linarith : 2 * nu < lambda),
      models_uniform_raw_defect hf hc hp ht hnu hd hR hR1 hRr1 hdelta hpaid,
      eventually_exp_decay_lt hp.2.1 hlambda hc.1,
      eventually_exp_decay_lt hp.2.1 hgamma hc.1,
      eventually_models_time_ge hf hp ht (max t0 Tgamma), (tendsto_atTop.1 hp.2.1) 0]
      with k hH hD hl hg htime hs
    exact ⟨hH, hD, hl, hg, htime, hs⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro a ha j haj z hz
  have hj := hN j (ha.trans haj)
  have haa := hN a ha
  have hz' : ‖z‖ ≤ Real.exp (-gamma * rho o (tk a)) := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hF := hregime (tk a) (tk j) ((le_max_right _ _).trans haa.2.2.2.2.1)
    (hp.1.monotone haj) z hz'
  refine ⟨by simpa only [neg_mul] using hj.1 _ hF, ?_⟩
  have hraw : ‖F (tk a) (tk j) z‖ ≤ Real.exp (-5 * nu * rho o (tk j)) := by
    apply hF.trans
    apply Real.exp_le_exp.mpr
    have hs := hj.2.2.2.2.2
    nlinarith
  have hcomp := shrinking_transition_cocycle_closedBall hc
    ((le_max_left _ _).trans haa.2.2.2.2.1) (hp.1.monotone haj)
    (hp.1.monotone (Nat.le_succ j)) (Real.exp_pos _).le haa.2.2.2.1
    (fun w hw => by
      have hw' : ‖w‖ ≤ Real.exp (-gamma * rho o (tk a)) := by
        simpa only [mem_closedBall, dist_zero_right] using hw
      have hh := hregime (tk a) (tk j) ((le_max_right _ _).trans haa.2.2.2.2.1)
        (hp.1.monotone haj) w hw'
      simpa only [mem_ball, dist_zero_right] using hh.trans_lt hj.2.2.1)
  have hD := hj.2.1 _ hraw
  rw [hcomp z hz] at hD
  exact hD

end Yau.NodeProofs.U02Proof
