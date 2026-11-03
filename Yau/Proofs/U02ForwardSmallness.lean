import Yau.Proofs.U02CorrectedOrbits

/-! The forward estimate on every original compact set follows from the
actual raw chart decay and the shadow of the same limit. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem compact_forward_smallness {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {sigmap : ℝ}
    (hsp : 0 < sigmap) (hsp1 : sigmap ≤ 1) (hsps : sigmap ≤ sigma)
    {psi : Pt X → ComplexVector n} {K : Set (Pt X)} (hK : IsCompact K)
    (hshadow : ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖(forwardComp G k).eval (psi x) - (H k).eval (f (tk k) x)‖ ≤
        Real.exp (-6 * rho o (tk k))) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖(forwardComp G k).eval (psi x)‖ ≤ Real.exp (-(sigmap / 2) * rho o (tk k)) := by
  have hmargin : 3 * sigmap / 4 < sigma := by linarith
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  filter_upwards [hshadow, corrected_compact_smallness hf hc hp ht hK hmargin,
    subexponential_times_decay hp.2.1 hconst 2 (3 * sigmap / 4) (sigmap / 2)
      (by linarith), (tendsto_atTop.1 hp.2.1) 0] with k hsh hH hsum hsk
  intro x hx
  have herror : Real.exp (-6 * rho o (tk k)) ≤
      Real.exp (-(3 * sigmap / 4) * rho o (tk k)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    ‖(forwardComp G k).eval (psi x)‖ ≤
        ‖(forwardComp G k).eval (psi x) - (H k).eval (f (tk k) x)‖ +
          ‖(H k).eval (f (tk k) x)‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * Real.exp (-(3 * sigmap / 4) * rho o (tk k)) := by
      have hh := add_le_add ((hsh x hx).trans herror) (hH x hx)
      simpa only [two_mul] using hh
    _ ≤ _ := by simpa only [zero_mul, Real.exp_zero, mul_one] using hsum

end Yau.NodeProofs.U02Proof
