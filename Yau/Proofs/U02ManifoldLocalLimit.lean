import Yau.Proofs.U02CompactLimit
import Yau.Proofs.U02ChartNeighborhood

/-! Read the local U01 limits on the actual manifold chart sheets. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem manifold_local_limits {n : ℕ} (hU01 : BackwardShadowing n n)
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P rho : STF X}
    {r0 r1 sigma C Cb t0 : ℝ} {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {nu R : ℝ}
    (hnu : 0 < nu) (hnu1 : nu < 1 / 10)
    (hd : 30 < ((d : ℝ) + 1) * nu) (hsigma : 5 * nu ≤ sigma)
    (hR : 0 < R) (hR1 : R ≤ 1) (hRr1 : R ≤ r1)
    (hhm : 0 < hm) (hsmall : Real.exp hm - 1 < 1 / 10)
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ nu / 4) :
    ∀ x : Pt X, ∃ V : Set (Pt X), IsOpen V ∧ x ∈ V ∧
      ∃ g : Pt X → ComplexVector n,
        ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ g V ∧
        TendstoUniformlyOn
          (fun l y => (backwardComp Ginv l).eval ((H l).eval (f (tk l) y))) g atTop V ∧
        ∀ᶠ k in atTop, ∀ y ∈ V,
          ‖(forwardComp G k).eval (g y) - (H k).eval (f (tk k) y)‖ ≤
            Real.exp (-6 * rho o (tk k)) := by
  intro x
  obtain ⟨r, hr, hclosed, hK, hkappa, V, hV, hxV, hVL, hsheet⟩ :=
    exists_compact_chart_neighborhood X.manifold x
  let Omega := ball (chartPt x x) (2 * r)
  let K := chartInv x '' closedBall (chartPt x x) (2 * r)
  have himage : Set.MapsTo (chartInv x) Omega K := by
    intro z hz
    exact ⟨z, ball_subset_closedBall hz, rfl⟩
  obtain ⟨psi, hpsi, hlimit, hshadow⟩ := corrected_compact_parameter_limit hU01
    hf hc hp ht hnu hnu1 hd hsigma hR hR1 hRr1 hhm hsmall hpaid hK isOpen_ball hkappa himage
  let g := fun y => psi (chartPt x y)
  have hL : closedBall (chartPt x x) r ⊆ Omega := closedBall_subset_ball (by linarith)
  have hmap : Set.MapsTo (chartPt x) V Omega := fun y hy => hL (hVL hy)
  have hchart : ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ (chartPt x) V := by
    apply (contMDiffOn_extChartAt (I := ComplexModel n) (n := ∞) (x := x)).mono
    intro y hy
    simpa only [extChartAt_source] using (hsheet y hy).1
  have hgsmooth : ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ g V :=
    (V03Proof.complex_holomorphic_contDiffOn isOpen_ball hpsi).contMDiffOn.comp hchart hmap
  have hlim := (hlimit (closedBall (chartPt x x) r) hL (isCompact_closedBall _ _)).comp (chartPt x)
  have hlimV := hlim.mono (show V ⊆ (chartPt x) ⁻¹' closedBall (chartPt x x) r from hVL)
  have hfull : TendstoUniformlyOn
      (fun l y => (backwardComp Ginv l).eval ((H l).eval (f (tk l) y))) g atTop V := by
    apply hlimV.congr
    apply Eventually.of_forall
    intro l y hy
    change (backwardComp Ginv l).eval ((H l).eval (f (tk l) (chartInv x (chartPt x y)))) = _
    rw [(hsheet y hy).2]
  refine ⟨V, hV, hxV, g, hgsmooth, hfull, ?_⟩
  filter_upwards [hshadow] with k hk
  intro y hy
  have hky := hk (chartPt x y) (hmap hy)
  rw [(hsheet y hy).2] at hky
  exact hky

end Yau.NodeProofs.U02Proof
