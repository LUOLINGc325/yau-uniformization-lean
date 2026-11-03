import Yau.Proofs.U02ManifoldLimit
import Yau.Proofs.U02Injectivity
import Yau.Proofs.U02Nonsingularity
import Yau.Proofs.U02OpenInverse
import Yau.Proofs.U02ForwardSmallness
import Yau.Proofs.U02InverseBall

/-! All parts of the original global-coordinate conclusion concern one
actual limit map, its own inverse, and the original polynomial sequence. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem global_coordinates_from_original_data {n : ℕ} (hU01 : BackwardShadowing n n)
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P rho : STF X}
    {r0 r1 sigma C Cb t0 : ℝ} {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho) (hw : RicciWindows X o h rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k)
    {nu R sigmap gamma gammap lambda Tgamma : ℝ}
    (hnu : 0 < nu) (hnu1 : nu < 1 / 10)
    (hd : 30 < ((d : ℝ) + 1) * nu) (hsigma : 5 * nu ≤ sigma)
    (hR : 0 < R) (hR1 : R ≤ 1) (hRr1 : R ≤ r1)
    (hhm : 0 < hm) (hsmall : Real.exp hm - 1 < 1 / 10)
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ nu / 4)
    (hsp : 0 < sigmap) (hsp1 : sigmap ≤ 1) (hsps : sigmap ≤ sigma)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (hgap : gamma < gammap)
    (hlambda : 0 < lambda) (hmargin : 5 * nu ≤ lambda)
    (hregime : ∀ t t', Tgamma ≤ t → t ≤ t' → ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-gamma * rho o t) → ‖F t t' z‖ ≤ Real.exp (-lambda * rho o t')) :
    ∃ psi inverse, GlobalCoordinates X o rho f tk H G Ginv sigmap gammap psi inverse := by
  obtain ⟨psi, hlimit, hpsi, hpsi0, hshadow⟩ := manifold_corrected_limit hU01 hf hc hp ht
    hnu hnu1 hd hsigma hR hR1 hRr1 hhm hsmall hpaid
  have hInj := corrected_limit_injective hf hw hc hp ht hshadow
  have hD : ∀ x : Pt X, Function.Bijective
      (fderiv ℂ (fun z => psi (chartInv x z)) (chartPt x x)) := by
    intro x
    have hi := corrected_limit_chart_derivative_injective hf hw hc hp ht hpsi hshadow x
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  obtain ⟨inverse, hopen, hinverse, hleft⟩ := U02OpenInverseAux.exists_global_inverse psi hpsi hInj hD
  have hchart := actual_chart_shadow hf hc hp ht hlimit hnu hnu1 hgamma hlambda hmargin hd
    hR hR1 hRr1 hsmall hpaid hregime
  have hball := inverse_ball_of_actual_chart_shadow hf hc hp ht hpsi hpsi0 hgamma hgamma1 hgap hchart
  refine ⟨psi, inverse, hlimit, hpsi, hInj, hpsi0, hopen, hinverse, hleft, ?_, hball⟩
  intro K hKr hK
  have hpre : IsCompact (inverse '' K) :=
    hK.image_of_continuousOn (hinverse.continuousOn.mono hKr)
  filter_upwards [compact_forward_smallness hf hc hp ht hsp hsp1 hsps hpre
    (hshadow _ hpre)] with k hk
  intro z hz
  obtain ⟨x, hx⟩ := hKr hz
  have hh := hk (inverse z) ⟨z, hz, rfl⟩
  simpa only [← hx, hleft x] using hh

end Yau.NodeProofs.U02Proof
