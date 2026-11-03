import Yau.Proofs.U02CorrectedOrbits
import Yau.Proofs.U02ModelDefect

/-! The two U01 orbit hypotheses on every fixed original compact set. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem corrected_compact_orbit {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {nu R : ℝ}
    (hnu : 0 < nu) (hd : 30 < ((d : ℝ) + 1) * nu) (hsigma : 5 * nu ≤ sigma)
    (hR : 0 < R) (hR1 : R ≤ 1) (hRr1 : R ≤ r1)
    (hdelta : Real.exp hm - 1 ≤ 1)
    (hpaid : |Cd| * (Real.exp hm - 1) ≤ 1 / 8)
    {K : Set (Pt X)} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖(H k).eval (f (tk k) x)‖ ≤ Real.exp (-2 * nu * rho o (tk k)) ∧
      ‖(H (k + 1)).eval (f (tk (k + 1)) x) - (G k).eval ((H k).eval (f (tk k) x))‖ ≤
        Real.exp (-10 * rho o (tk k)) := by
  have hmargin : 2 * nu < sigma := by nlinarith
  filter_upwards [corrected_compact_smallness hf hc hp ht hK hmargin,
    raw_compact_data hf hc hp ht hK, raw_compact_orbit hf hc hp ht hK,
    models_uniform_raw_defect hf hc hp ht hnu hd hR hR1 hRr1 hdelta hpaid,
    (tendsto_atTop.1 hp.2.1) 0] with k hsmall hraw horbit hdefect hsk
  obtain ⟨V, _hV, _hKV, _hdf, _hv, hdecay⟩ := hraw
  intro x hx
  refine ⟨by simpa only [neg_mul] using hsmall x hx, ?_⟩
  rw [horbit x hx]
  apply hdefect (f (tk k) x)
  apply (hdecay x hx).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hsigma hsk
  nlinarith

theorem corrected_pullback_differentiable {n m : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {K : Set (Pt X)} (hK : IsCompact K)
    {Omega : Set (ComplexVector m)} {kappa : ComplexVector m → Pt X}
    (hkappa : MDifferentiableOn 𝓘(ℂ, ComplexVector m) (ComplexModel n) kappa Omega)
    (himage : Set.MapsTo kappa Omega K) :
    ∀ᶠ k in atTop,
      DifferentiableOn ℂ (fun z => (H k).eval (f (tk k) (kappa z))) Omega := by
  filter_upwards [raw_compact_data hf hc hp ht hK] with k hk
  obtain ⟨V, _hV, hKV, hdf, _hv, _hdecay⟩ := hk
  have hmap : Omega ⊆ kappa ⁻¹' V := fun z hz => hKV (himage hz)
  have hraw := (hdf.comp hkappa hmap).differentiableOn
  exact ((polynomial_contDiff (H k)).differentiable (by simp)).comp_differentiableOn hraw

end Yau.NodeProofs.U02Proof
