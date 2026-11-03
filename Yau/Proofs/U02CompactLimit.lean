import Yau.Proofs.U02LocalLimit
import Yau.Proofs.U02CompactOrbit
import Yau.Proofs.U02InverseTube

/-! The original corrected coordinate sequence converges on each
holomorphic parameter domain whose image lies in one compact of M. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem corrected_compact_parameter_limit {n m : ℕ}
    (hU01 : BackwardShadowing n m) {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
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
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ nu / 4)
    {K : Set (Pt X)} (hK : IsCompact K)
    {Omega : Set (ComplexVector m)} (hOmega : IsOpen Omega)
    {kappa : ComplexVector m → Pt X}
    (hkappa : MDifferentiableOn 𝓘(ℂ, ComplexVector m) (ComplexModel n) kappa Omega)
    (himage : Set.MapsTo kappa Omega K) :
    ∃ psi : ComplexVector m → ComplexVector n,
      DifferentiableOn ℂ psi Omega ∧
      (∀ L ⊆ Omega, IsCompact L → TendstoUniformlyOn
        (fun l z => (backwardComp Ginv l).eval ((H l).eval (f (tk l) (kappa z)))) psi atTop L) ∧
      ∀ᶠ k in atTop, ∀ z ∈ Omega,
        ‖(forwardComp G k).eval (psi z) - (H k).eval (f (tk k) (kappa z))‖ ≤
          Real.exp (-6 * rho o (tk k)) := by
  have hdelta : 0 < Real.exp hm - 1 := by
    have hh := Real.one_lt_exp_iff.mpr hhm
    linarith
  have hpaid8 : |Cd| * (Real.exp hm - 1) ≤ 1 / 8 := hpaid.trans (by linarith)
  apply backwardShadowing_local_limit hU01 hOmega hnu hnu1 hdelta hsmall hp.2.1
    (models_unit_spacing hp)
  · intro k
    exact (hp.2.2.2.2.1 k).2.2.2.2.1
  · intro k
    exact hp.2.2.2.2.2.2.2.2.2 k
  · exact corrected_pullback_differentiable hf hc hp ht hK hkappa himage
  · filter_upwards [corrected_compact_orbit hf hc hp ht hnu hd hsigma hR hR1 hRr1
      (by linarith : Real.exp hm - 1 ≤ 1) hpaid8 hK] with k hk
    intro z hz
    exact hk (kappa z) (himage hz)
  · exact models_inverse_tube hp hnu hpaid

end Yau.NodeProofs.U02Proof
