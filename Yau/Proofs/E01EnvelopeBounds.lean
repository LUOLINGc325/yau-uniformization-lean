import Yau.Proofs.E01RawUpper
import Yau.Proofs.E01RawLower
import Yau.Proofs.V03Envelope

/-! Exact actual cometric bounds for the original chart envelope.
The lower bound alone is conditional on the separate genuine initial circle-mean theorem. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ}

theorem envelopeChart_le_actual_dualNormChart {M : ComplexManifold n}
    (h : ℝ → HermitianField M) (T : ℝ) (x : M.Carrier) (z η : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T) :
    envelopeChart h T x (z, η, t) ≤ (dualNormChart (h t) x z η : EReal) := by
  have hu := envelopeRaw_le_actual_dualNorm h T (chartInv x z)
    (covectorOfCoords x (chartInv x z) η) t ht.1 ht.2
  have hc := dualNorm_cotangentChartInv (h t) x
    (z := (z, η)) ⟨hz, Set.mem_univ η⟩
  change dualNorm (h t) (chartInv x z) (covectorOfCoords x (chartInv x z) η) =
    dualNormChart (h t) x z η at hc
  rw [hc] at hu
  have he : envelopeChart h T x (z, η, t) ≤ envelopeRawChart h T x (z, η, t) :=
    liminf_nhdsWithin_le_self (envelopeRawChart h T x) ⟨hz, ht⟩
  exact he.trans hu

theorem envelopeChart_lower_of_initial_circle_mean {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {U P ρ : STF X} (hloc : LocalizedFlow X o h U P ρ)
    (hmean : ∀ (f : ℂ → Pt X) (ξd : ℂ → Covector n), IsCotangentDisc f ξd →
      dualNorm X.metric.form (f 0) (ξd 0) ≤ circleAverage (fun θ =>
        dualNorm X.metric.form (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))))
    (T : ℝ) (x : Pt X) (z η : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T) :
    (dualNormChart X.metric.form x z η : EReal) ≤ envelopeChart h T x (z, η, t) := by
  let S : Set (ComplexVector n × ComplexVector n × ℝ) :=
    {q | q.1 ∈ chartTarget x ∧ q.2.2 ∈ Ioo 0 T}
  let N : ComplexVector n × ComplexVector n × ℝ → ℝ :=
    fun q => dualNormChart X.metric.form x q.1 q.2.1
  have hp : (z, η, t) ∈ S := ⟨hz, ht⟩
  have hc : Continuous (fun q : ComplexVector n × ComplexVector n × ℝ => (q.1, q.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hQ : ContinuousOn
      (fun p : CotangentCoord n => dualNormChart X.metric.form x p.1 p.2)
      (cotangentTarget x) := (dualNormChart_contDiffOn X.metric x).continuousOn
  have hmap : MapsTo (fun q : ComplexVector n × ComplexVector n × ℝ => (q.1, q.2.1))
      S (cotangentTarget x) := fun q hq => ⟨hq.1, Set.mem_univ q.2.1⟩
  have hN : ContinuousOn N S := by
    change ContinuousOn (fun q : ComplexVector n × ComplexVector n × ℝ =>
      dualNormChart X.metric.form x q.1 q.2.1) S
    have hcont : ContinuousOn
        (fun q : ComplexVector n × ComplexVector n × ℝ => (q.1, q.2.1)) S :=
      hc.continuousOn
    exact ContinuousOn.comp'
      (g := fun p : CotangentCoord n => dualNormChart X.metric.form x p.1 p.2)
      (f := fun q : ComplexVector n × ComplexVector n × ℝ => (q.1, q.2.1))
      (s := S) (t := cotangentTarget x) hQ hcont hmap
  haveI : NeBot (𝓝[S] (z, η, t)) := nhdsWithin_neBot_of_mem hp
  have hNt : Tendsto N (𝓝[S] (z, η, t)) (𝓝 (N (z, η, t))) := hN _ hp
  have hE : Tendsto (fun q => (N q : EReal)) (𝓝[S] (z, η, t))
      (𝓝 (N (z, η, t) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hNt
  change (N (z, η, t) : EReal) ≤ liminf (envelopeRawChart h T x) (𝓝[S] (z, η, t))
  have hlim : liminf (fun q => (N q : EReal)) (𝓝[S] (z, η, t)) =
      (N (z, η, t) : EReal) := hE.liminf_eq
  rw [← hlim]
  have hpoint : ∀ᶠ q in 𝓝[S] (z, η, t), (N q : EReal) ≤ envelopeRawChart h T x q := by
    have hmem : ∀ᶠ q in 𝓝[S] (z, η, t), q ∈ S := self_mem_nhdsWithin
    filter_upwards [hmem] with q hq
    have hl := envelopeRaw_lower_of_initial_circle_mean hloc hmean T
      (chartInv x q.1) (covectorOfCoords x (chartInv x q.1) q.2.1) q.2.2
    have hqnorm := dualNorm_cotangentChartInv X.metric.form x
      (z := (q.1, q.2.1)) ⟨hq.1, Set.mem_univ q.2.1⟩
    change dualNorm X.metric.form (chartInv x q.1)
      (covectorOfCoords x (chartInv x q.1) q.2.1) = N q at hqnorm
    change (N q : EReal) ≤ envelopeRaw h T (chartInv x q.1)
      (covectorOfCoords x (chartInv x q.1) q.2.1) q.2.2
    simpa only [hqnorm] using hl
  exact liminf_le_liminf hpoint

end Yau.NodeProofs.E01Aux
