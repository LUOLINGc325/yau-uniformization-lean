import Yau.Proofs.U02RawCharts
import Yau.Proofs.U02SmallPolynomials

/-! The corrected compact-regime orbit uses the original raw inverse
charts and the original polynomial `H_k`. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem polynomial_fixesZero_eval_zero {n : ℕ} (P : PolyMap n) (hP : P.FixesZero) :
    P.eval 0 = 0 := by
  ext i
  simpa [PolyMap.eval, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] using hP i

theorem corrected_compact_smallness {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {K : Set (Pt X)} (hK : IsCompact K)
    {b : ℝ} (hb : b < sigma) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖(H k).eval (f (tk k) x)‖ ≤ Real.exp (-b * rho o (tk k)) := by
  filter_upwards [raw_compact_data hf hc hp ht hK,
    model_H_small_ball hp hc.2.2.1 hb] with k hk hH
  obtain ⟨V, _hV, _hKV, _hdf, _hv, hdecay⟩ := hk
  intro x hx
  exact hH (f (tk k) x) (hdecay x hx)

theorem corrected_basepoint_zero {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) :
    ∀ᶠ k in atTop, (H k).eval (f (tk k) o) = 0 := by
  filter_upwards [raw_basepoint_zero hf hc hp ht] with k hk
  rw [hk]
  exact polynomial_fixesZero_eval_zero (H k) (hp.2.2.2.2.1 k).1

end Yau.NodeProofs.U02Proof
