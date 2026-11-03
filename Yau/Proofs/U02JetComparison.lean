import Yau.Proofs.U02ZeroJets
import Yau.Proofs.U02PolynomialGlobalBounds

/-! A uniform raw-ball estimate for the literal conjugacy difference.
The only jet premise is the original `GermJetEq`. -/

open scoped Topology ContDiff
open Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau

theorem jet_comparison_bound {n d : ℕ} {f g : ComplexVector n → ComplexVector n}
    {R A : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℂ ∞ f (ball 0 R)) (hg : ContDiffOn ℂ ∞ g (ball 0 R))
    (hjet : GermJetEq f g d)
    (hbound : ∀ z ∈ ball (0 : ComplexVector n) R, ‖f z - g z‖ ≤ A)
    {z : ComplexVector n} (hz : ‖z‖ < R) :
    ‖f z - g z‖ ≤ A * (‖z‖ / R) ^ (d + 1) := by
  have hfa : ContDiffAt ℂ ∞ f 0 :=
    (hf 0 (mem_ball_self hR)).contDiffAt (ball_mem_nhds _ hR)
  have hga : ContDiffAt ℂ ∞ g 0 :=
    (hg 0 (mem_ball_self hR)).contDiffAt (ball_mem_nhds _ hR)
  have hzero : ∀ k ≤ d, iteratedFDeriv ℂ k (fun w => f w - g w) 0 = 0 := by
    intro k hk
    change iteratedFDeriv ℂ k (f - g) 0 = 0
    rw [iteratedFDeriv_sub_apply (hfa.of_le (by simp)) (hga.of_le (by simp)),
      hjet k hk, sub_self]
  exact zeroJet_schwarz_bound hR (hf.sub hg) hzero hbound hz

theorem polynomial_jet_conjugacy_bound {n d D : ℕ}
    (Hnext G H : PolyMap n) {F : ComplexVector n → ComplexVector n} {R B : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hB : 1 ≤ B) (hD : Hnext.degree ≤ D)
    (hF : ContDiffOn ℂ ∞ F (ball 0 R))
    (hFb : ∀ z ∈ ball (0 : ComplexVector n) R, ‖F z‖ ≤ B)
    (hjet : GermJetEq (fun z => Hnext.eval (F z)) (fun z => G.eval (H.eval z)) d)
    {z : ComplexVector n} (hz : ‖z‖ < R) :
    ‖Hnext.eval (F z) - G.eval (H.eval z)‖ ≤
      (Hnext.coeffNorm * B ^ D + (G.comp H).coeffNorm) * (‖z‖ / R) ^ (d + 1) := by
  have hH : ContDiffOn ℂ ∞ Hnext.eval Set.univ :=
    (polynomial_contDiff Hnext).of_le le_top |>.contDiffOn
  have hfirst : ContDiffOn ℂ ∞ (fun z => Hnext.eval (F z)) (ball 0 R) :=
    hH.comp hF (by intro z hz; trivial)
  have hsecond : ContDiffOn ℂ ∞ (fun z => G.eval (H.eval z)) (ball 0 R) :=
    ((polynomial_contDiff G).comp (polynomial_contDiff H)).of_le le_top |>.contDiffOn
  apply jet_comparison_bound hR hfirst hsecond hjet _ hz
  intro w hw
  have hfirstBound := polynomial_fixed_degree_bound Hnext hD hB (hFb w hw)
  have hw1 : ‖w‖ ≤ 1 := (show ‖w‖ < R by simpa using hw).le.trans hR1
  have hsecondBound : ‖G.eval (H.eval w)‖ ≤ (G.comp H).coeffNorm := by
    rw [← polynomial_eval_comp]
    simpa only [pow_zero, mul_one] using polynomial_norm_le (q := 0) (G.comp H)
      (fun i m hm => False.elim (by omega)) hw1
  exact (norm_sub_le _ _).trans (add_le_add hfirstBound hsecondBound)

end Yau.NodeProofs.U02Proof
