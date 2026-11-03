import Yau.Proofs.U02TransitionContinuation
import Yau.Proofs.U02RawCharts

/-! On a fixed compact image of an original chart sheet, the late raw
inverse is the same geometric transition throughout the closed ball. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem unitaryChart_compact_image {n : ℕ} {M : ComplexManifold n}
    {h : HermitianField M} {p : M.Carrier} {Phi : ComplexVector n → M.Carrier}
    {r c C R : ℝ} (hc : UnitaryChart h p Phi r c C) (hR : R < r) :
    IsCompact (Phi '' closedBall (0 : ComplexVector n) R) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    (hc.1.1.continuousOn.mono (closedBall_subset_ball hR))

theorem late_inverse_chart_pullback {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {t R : ℝ}
    (ht0 : t0 ≤ t) (hR : 0 ≤ R) (hR1 : R < r1) :
    ∀ᶠ l in atTop, ∀ z ∈ closedBall (0 : ComplexVector n) R,
      f (tk l) (Phi t z) = F t (tk l) z := by
  let K := Phi t '' closedBall (0 : ComplexVector n) R
  have hchart := hc.2.2.2.2.1 t ht0
  have hK : IsCompact K := unitaryChart_compact_image hchart (hR1.trans hc.2.1)
  have hoK : o ∈ K := ⟨0, mem_closedBall_self hR, hchart.2.1⟩
  filter_upwards [raw_compact_data hf hc hp ht hK,
    eventually_models_time_ge hf hp ht t] with l hl htime
  obtain ⟨V, hV, hKV, hdf, hinv, _hdecay⟩ := hl
  exact shrinking_inverse_transition_closedBall hc ht0 htime hR hR1 hV (hKV hoK) hdf
    (fun x hx => (hinv x hx).2.1) (fun z hz => hKV ⟨z, hz, rfl⟩)

end Yau.NodeProofs.U02Proof
