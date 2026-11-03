import Yau.Proofs.U02RawChartPullback
import Yau.Proofs.U02TailAlgebra

/-! Pass the finite inverse-segment bound to the actual global coordinate
map on the same original chart sheet, clock, and polynomial prefix. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem finite_chart_shadow_limit {n : ℕ} {X : KahlerManifold n} {o : Pt X}
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
    {a : ℕ} {r eps : ℝ} (ha : t0 ≤ tk a) (hr : 0 ≤ r) (hrr : r < r1)
    (hfinite : ∀ l, a ≤ l → ∀ z ∈ closedBall (0 : ComplexVector n) r,
      ‖(backwardSegment Ginv a (l - a)).eval ((H l).eval (F (tk a) (tk l) z)) -
        (H a).eval z‖ ≤ eps) :
    ∀ z ∈ closedBall (0 : ComplexVector n) r,
      ‖(forwardComp G a).eval (psi (Phi (tk a) z)) - (H a).eval z‖ ≤ eps := by
  let K := Phi (tk a) '' closedBall (0 : ComplexVector n) r
  have hK : IsCompact K := unitaryChart_compact_image
    (hc.2.2.2.2.1 (tk a) ha) (hrr.trans hc.2.1)
  have hpull := late_inverse_chart_pullback hf hc hp ht ha hr hrr
  intro z hz
  have hpoint := (hlimit K hK).tendsto_at (show Phi (tk a) z ∈ K from ⟨z, hz, rfl⟩)
  have hforward := ((polynomial_contDiff (forwardComp G a)).continuous.tendsto
    (psi (Phi (tk a) z))).comp hpoint
  apply le_of_tendsto (hforward.sub_const ((H a).eval z)).norm
  filter_upwards [hpull, eventually_ge_atTop a] with l hl hal
  have hh := hfinite l hal z hz
  rw [← hl z hz] at hh
  rw [← forward_cancel_backward_tail G Ginv a l hal
    (hp.2.2.2.2.2.2.2.2.2 a)] at hh
  exact hh

end Yau.NodeProofs.U02Proof
