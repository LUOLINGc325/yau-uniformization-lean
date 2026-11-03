import Yau.Proofs.U02ManifoldLocalLimit
import Yau.Proofs.U02CompactUniform
import Yau.Proofs.U02LimitPatch

/-! One global corrected-coordinate limit on the original manifold,
with compact-uniform convergence and the original forward shadow. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem models_backward_prefix_zero {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv) :
    ∀ k, (backwardComp Ginv k).eval 0 = 0 := by
  intro k
  induction k with
  | zero => exact polynomial_eval_id 0
  | succ k ih =>
    have hn := hp.2.2.2.2.1 k
    have hQ := automorphism_inverse_fixesZero hn.2.2.2.2.1 hn.2.2.2.1
    rw [backwardComp, polynomial_eval_comp, polynomial_fixesZero_eval_zero (Ginv k) hQ, ih]

theorem manifold_corrected_limit {n : ℕ} (hU01 : BackwardShadowing n n)
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
    ∃ psi : Pt X → ComplexVector n,
      (∀ K : Set (Pt X), IsCompact K → TendstoUniformlyOn
        (fun l x => (backwardComp Ginv l).eval ((H l).eval (f (tk l) x))) psi atTop K) ∧
      ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ psi ∧ psi o = 0 ∧
      ∀ K : Set (Pt X), IsCompact K → ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖(forwardComp G k).eval (psi x) - (H k).eval (f (tk k) x)‖ ≤
          Real.exp (-6 * rho o (tk k)) := by
  let seq := fun l x => (backwardComp Ginv l).eval ((H l).eval (f (tk l) x))
  have hlocal := manifold_local_limits hU01 hf hc hp ht hnu hnu1 hd hsigma
    hR hR1 hRr1 hhm hsmall hpaid
  have hpatch : ∀ x : Pt X, ∃ V ∈ 𝓝 x, ∃ g : Pt X → ComplexVector n,
      TendstoUniformlyOn seq g atTop V := by
    intro x
    obtain ⟨V, hV, hxV, g, _hg, hlim, _hshadow⟩ := hlocal x
    exact ⟨V, hV.mem_nhds hxV, g, hlim⟩
  obtain ⟨psi, hpoint, _hlu, hcompact⟩ := patch_local_uniform_limits seq hpatch
  have hlocalPsi : ∀ x : Pt X, ∃ V : Set (Pt X), IsOpen V ∧ x ∈ V ∧
      ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ psi V ∧
      ∀ᶠ k in atTop, ∀ y ∈ V,
        ‖(forwardComp G k).eval (psi y) - (H k).eval (f (tk k) y)‖ ≤
          Real.exp (-6 * rho o (tk k)) := by
    intro x
    obtain ⟨V, hV, hxV, g, hg, hlim, hshadow⟩ := hlocal x
    have heq : ∀ y ∈ V, psi y = g y := fun y hy =>
      tendsto_nhds_unique (hpoint y) (hlim.tendsto_at hy)
    refine ⟨V, hV, hxV, hg.congr heq, ?_⟩
    filter_upwards [hshadow] with k hk
    intro y hy
    rw [heq y hy]
    exact hk y hy
  have hpsismooth : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ psi := by
    intro x
    obtain ⟨V, hV, hxV, hg, _hshadow⟩ := hlocalPsi x
    exact (hg x hxV).contMDiffAt (hV.mem_nhds hxV)
  have hzero : ∀ᶠ k in atTop, seq k o = 0 := by
    filter_upwards [raw_basepoint_zero hf hc hp ht] with k hk
    dsimp only [seq]
    rw [hk, polynomial_fixesZero_eval_zero (H k) (hp.2.2.2.2.1 k).1,
      models_backward_prefix_zero hp k]
  have hzeroLimit : Tendsto (fun k => seq k o) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ hk => hk.symm)
  refine ⟨psi, hcompact, hpsismooth, tendsto_nhds_unique (hpoint o) hzeroLimit, ?_⟩
  intro K hK
  apply compact_eventually_of_local _ hK
  intro x
  obtain ⟨V, hV, hxV, _hg, hshadow⟩ := hlocalPsi x
  exact ⟨V, hV.mem_nhds hxV, hshadow⟩

end Yau.NodeProofs.U02Proof
