import Yau.LeafProofs.L05ChuResidual

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuFrozenResidual {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) (u : Point n → ℝ) (p : Point n) : ℝ :=
  timeD (backward 1) u p-chuFrozenLinear hT F A0 p0 hp0 (hessian u p)

theorem chuFrozenResidual_sub {n : ℕ} {T : Sym n → Point n → Sym n}
    {K beta : ℝ} (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ)
    (S : Point n → Sym n) (A0 : Sym n) (p0 : Point n) (hp0 : p0 ∈ backward 1)
    (f u : Point n → ℝ)
    (hPDE : ∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p)
    {p q : Point n} (hp : p ∈ backward 1) (hq : q ∈ backward 1) :
    chuFrozenResidual hT F A0 p0 hp0 u p-chuFrozenResidual hT F A0 p0 hp0 u q=
      (f p-f q)+(F (S p+T (hessian u p) p) p-F (S q+T (hessian u q) q) q-
        chuFrozenLinear hT F A0 p0 hp0 (hessian u p-hessian u q)) := by
  have hl := (chuFrozenLinear hT F A0 p0 hp0).map_sub (hessian u p) (hessian u q)
  dsimp only [chuFrozenResidual]
  linarith only [hPDE p hp,hPDE q hq,hl]

set_option maxHeartbeats 1600000 in
theorem chuFrozenResidual_difference {n : ℕ} {E U : Set (Sym n)} (hE : Convex ℝ E)
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {S : Point n → Sym n}
    {ell L K alpha beta fB : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    {omega : ℝ → ℝ} (hm : Modulus omega) (hDF : ChuDerivativeModulus E F omega)
    {A0 : Sym n} (hA0 : A0 ∈ E) {p0 : Point n} (hp0 : p0 ∈ backward 1)
    {f u : Point n → ℝ} (hf : HolderBound alpha (backward 1) f fB)
    (hRange : ∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E)
    (hPDE : ∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p)
    {p q : Point n} (hp : p ∈ backward 1) (hq : q ∈ backward 1)
    {delta : ℝ} (hd : 0 ≤ delta) (hAd : ‖S p+T (hessian u p) p-A0‖ ≤ delta)
    (hBd : ‖S q+T (hessian u q) q-A0‖ ≤ delta) :
    |chuFrozenResidual hT F A0 p0 hp0 u p-chuFrozenResidual hT F A0 p0 hp0 u q| ≤
      fB*holderWeight alpha p q+
      (omega (delta+parabolicDistance p p0)*chuTransformNormConstant n K+
        2*bellmanMatrixConstant n L*K*holderWeight beta p p0)*‖hessian u p-hessian u q‖+
      (K+(omega (delta+parabolicDistance p p0)+bellmanMatrixConstant n L)*K*(1+2*‖hessian u q‖))*
        holderWeight beta p q := by
  have hn := chu_frozen_nonlinear_error hE hell hL hK hF hT hS hm hDF hA0 hp hq hp0
    (hRange p hp) (hRange q hq) hd hAd hBd
  have hfd : |f p-f q| ≤ fB*holderWeight alpha p q := by
    simpa only [Real.norm_eq_abs] using hf.2.2 p hp q hq
  rw [chuFrozenResidual_sub hT F S A0 p0 hp0 f u hPDE hp hq]
  have ht := abs_add_le (f p-f q) (F (S p+T (hessian u p) p) p-F (S q+T (hessian u q) q) q-
    chuFrozenLinear hT F A0 p0 hp0 (hessian u p-hessian u q))
  linarith only [ht,hfd,hn]

end Yau.LeafProofs.L05Aux
