import Yau.Proofs.V03DualNorm
import Yau.Proofs.V03Walls

/-! The original raw envelope bounds each admissible disc. Its neighborhood
liminf is a lower semicontinuous minorant in the actual coordinate domain. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem liminf_nhdsWithin_le_self {α : Type*} [TopologicalSpace α]
    (f : α → EReal) {S : Set α} {x : α} (hx : x ∈ S) :
    liminf f (𝓝[S] x) ≤ f x := by
  apply liminf_le_of_frequently_le'
  by_contra h
  have hn := not_frequently.mp h
  exact (hn.self_of_nhdsWithin hx) le_rfl

theorem lowerSemicontinuousOn_liminf_nhdsWithin {α : Type*} [TopologicalSpace α]
    (f : α → EReal) (S : Set α) :
    LowerSemicontinuousOn (fun x => liminf f (𝓝[S] x)) S := by
  intro x hx a ha
  change a < sSup {b : EReal | ∀ᶠ y in 𝓝[S] x, b ≤ f y} at ha
  obtain ⟨b, hb, hab⟩ := lt_sSup_iff.mp ha
  obtain ⟨U, hU, hxU, hUb⟩ := mem_nhdsWithin.mp hb
  have hUnear : U ∈ 𝓝[S] x := mem_nhdsWithin.mpr ⟨U, hU, hxU, Set.inter_subset_left⟩
  filter_upwards [hUnear] with y hy
  apply hab.trans_le
  change b ≤ sSup {c : EReal | ∀ᶠ z in 𝓝[S] y, c ≤ f z}
  exact le_sSup (mem_nhdsWithin.mpr ⟨U, hU, hy, hUb⟩)

theorem envelopeRaw_nonneg (h : Flow X) (T : ℝ)
    (y : Pt X) (ξ : Covector n) (s : ℝ) :
    0 ≤ envelopeRaw h T y ξ s := by
  unfold envelopeRaw
  refine le_iInf fun f => le_iInf fun ξd => le_iInf fun w => le_iInf fun _ => ?_
  exact EReal.coe_nonneg.mpr (circleAverage_nonneg (fun θ => dualNorm_nonneg _ _ _))

theorem envelopeChart_nonneg (h : Flow X) (T : ℝ) (x : Pt X)
    (p : ComplexVector n × ComplexVector n × ℝ) :
    0 ≤ envelopeChart h T x p := by
  unfold envelopeChart
  change (0 : EReal) ≤ sSup {b : EReal | ∀ᶠ z in
    𝓝[{q : ComplexVector n × ComplexVector n × ℝ |
      q.1 ∈ chartTarget x ∧ 0 < q.2.2 ∧ q.2.2 < T}] p,
    b ≤ envelopeRawChart h T x z}
  apply le_sSup
  change ∀ᶠ z in
    𝓝[{q : ComplexVector n × ComplexVector n × ℝ |
      q.1 ∈ chartTarget x ∧ 0 < q.2.2 ∧ q.2.2 < T}] p,
    (0 : EReal) ≤ envelopeRawChart h T x z
  exact Eventually.of_forall fun z => envelopeRaw_nonneg h T
    (chartInv x z.1) (covectorOfCoords x (chartInv x z.1) z.2.1) z.2.2

theorem envelopeChart_le_raw (h : Flow X) (T : ℝ) (x : Pt X)
    (p : ComplexVector n × ComplexVector n × ℝ)
    (hp : p.1 ∈ chartTarget x ∧ 0 < p.2.2 ∧ p.2.2 < T) :
    envelopeChart h T x p ≤ envelopeRawChart h T x p :=
  liminf_nhdsWithin_le_self _ hp

theorem envelopeChart_lowerSemicontinuousOn (h : Flow X) (T : ℝ) (x : Pt X) :
    LowerSemicontinuousOn (envelopeChart h T x)
      {p : ComplexVector n × ComplexVector n × ℝ |
        p.1 ∈ chartTarget x ∧ 0 < p.2.2 ∧ p.2.2 < T} :=
  lowerSemicontinuousOn_liminf_nhdsWithin _ _

theorem envelopeRaw_le_disc_average {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    envelopeRaw d.h d.T (F.f 0).1 (F.f 0).2 F.s ≤
      (circleAverage (fun θ => let y := F.f (circlePoint θ)
        dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2) : EReal) := by
  obtain ⟨hf, hw, hw0, hs, hsT, _, ht, _, _⟩ := hF
  unfold envelopeRaw
  refine iInf_le_of_le (fun ζ => (F.f ζ).1)
    (iInf_le_of_le (fun ζ => (F.f ζ).2) (iInf_le_of_le F.w (iInf_le _ ?_)))
  exact ⟨hs, hsT, hf, hw, rfl, rfl, hw0, ht⟩

set_option maxHeartbeats 800000 in
theorem contact_test_le_disc_average {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    d.test (F.f 0) F.s ≤ circleAverage (fun θ => let y := F.f (circlePoint θ)
      dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2) := by
  have hc := hF.2.2.2.2.2.1
  have hcontact := hd.2.2.2.2.2.2.2.1
  have hvalid := hcontact.2.2.1 hc.2
  have htest := hcontact.2.2.2.1 _ hc.2
  have hraw := envelopeChart_le_raw d.h d.T d.chart
    ((cotangentChart d.chart (F.f 0)).1,
      (cotangentChart d.chart (F.f 0)).2, F.s) ⟨hvalid.1.1, hvalid.2⟩
  have hround := cotangentChart_left_inv d.chart hc.1
  have heq : envelopeRawChart d.h d.T d.chart
      ((cotangentChart d.chart (F.f 0)).1,
        (cotangentChart d.chart (F.f 0)).2, F.s) =
      envelopeRaw d.h d.T (F.f 0).1 (F.f 0).2 F.s := by
    change envelopeRaw d.h d.T
      (cotangentChartInv d.chart (cotangentChart d.chart (F.f 0))).1
      (cotangentChartInv d.chart (cotangentChart d.chart (F.f 0))).2 F.s = _
    rw [hround]
  rw [hround] at htest
  exact EReal.coe_le_coe_iff.mp
    (htest.trans (hraw.trans (heq.le.trans (envelopeRaw_le_disc_average hF))))

end Yau.Blueprint.V03Proof
