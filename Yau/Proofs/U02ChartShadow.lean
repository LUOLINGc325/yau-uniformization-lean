import Yau.Proofs.U02RegimeOrbit
import Yau.Proofs.U02FiniteShadow
import Yau.Proofs.U02ChartShadowLimit

/-! The regime (ii) shadow is uniform in the late starting index and is
linked to the actual global limit on the same original immersed chart. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem actual_chart_shadow {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {psi : Pt X → ComplexVector n}
    (hlimit : ∀ K : Set (Pt X), IsCompact K → TendstoUniformlyOn
      (fun l x => (backwardComp Ginv l).eval ((H l).eval (f (tk l) x))) psi atTop K)
    {nu gamma lambda Tgamma R : ℝ}
    (hnu : 0 < nu) (hnu1 : nu < 1 / 10) (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hmargin : 5 * nu ≤ lambda) (hd : 30 < ((d : ℝ) + 1) * nu)
    (hR : 0 < R) (hR1 : R ≤ 1) (hRr1 : R ≤ r1)
    (hsmall : Real.exp hm - 1 < 1 / 10) (hpaid : |Cd| * (Real.exp hm - 1) ≤ nu / 4)
    (hregime : ∀ t t', Tgamma ≤ t → t ≤ t' → ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-gamma * rho o t) → ‖F t t' z‖ ≤ Real.exp (-lambda * rho o t')) :
    ∀ᶠ a in atTop, ∀ z ∈ closedBall (0 : ComplexVector n)
      (Real.exp (-gamma * rho o (tk a))),
      ‖(forwardComp G a).eval (psi (Phi (tk a) z)) - (H a).eval z‖ ≤
        Real.exp (-6 * rho o (tk a)) := by
  have horbit := regime_two_corrected_orbit hf hc hp ht hnu hgamma hlambda hmargin hd
    hR hR1 hRr1 (by linarith : Real.exp hm - 1 ≤ 1)
    (hpaid.trans (by linarith : nu / 4 ≤ 1 / 8)) hregime
  have hfinite := finite_shadow_on_late_tails hnu hnu1 hsmall hp.2.1
    (models_unit_spacing hp) (fun k => (hp.2.2.2.2.1 k).2.2.2.2.1) horbit
    (models_inverse_tube hp hnu hpaid)
  filter_upwards [hfinite, eventually_models_time_ge hf hp ht t0,
    eventually_exp_decay_lt hp.2.1 hgamma hc.1, (tendsto_atTop.1 hp.2.1) 0]
    with a hfa hta hrr hsa
  have hself := shrinking_transition_self hc hta
  have hbound : ∀ l, a ≤ l → ∀ z ∈ closedBall (0 : ComplexVector n)
      (Real.exp (-gamma * rho o (tk a))),
      ‖(backwardSegment Ginv a (l - a)).eval ((H l).eval (F (tk a) (tk l) z)) -
        (H a).eval z‖ ≤ Real.exp (-7 * rho o (tk a)) := by
    intro l hal z hz
    have hh := hfa l hal z hz
    rw [hself (closedBall_subset_ball hrr hz)] at hh
    exact hh
  intro z hz
  exact (finite_chart_shadow_limit hf hc hp ht hlimit hta (Real.exp_pos _).le hrr hbound z hz).trans
    (Real.exp_le_exp.mpr (by linarith))

end Yau.NodeProofs.U02Proof
