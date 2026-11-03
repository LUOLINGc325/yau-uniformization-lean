import Yau.Proofs.V03CotangentSmooth

/-! SOURCE-ONLY E03 candidate. Every transition is the actual induced cotangent transition. -/

noncomputable section
open scoped Manifold Topology ContDiff
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

def spaceTimeChartChange (c d : M.Carrier)
    (p : ComplexVector n × ComplexVector n × ℝ) :
    ComplexVector n × ComplexVector n × ℝ :=
  let q := cotangentChart d (cotangentChartInv c (p.1, p.2.1))
  (q.1, q.2, p.2.2)

theorem envelopeRawChart_change (h : ℝ → HermitianField M) (T : ℝ)
    (c d : M.Carrier) (p : ComplexVector n × ComplexVector n × ℝ)
    (hd : chartInv c p.1 ∈ (extChartAt (ComplexModel n) d).source) :
    envelopeRawChart h T d (spaceTimeChartChange c d p) = envelopeRawChart h T c p := by
  have hi := cotangentChart_left_inv d (y := cotangentChartInv c (p.1, p.2.1)) hd
  change envelopeRaw h T
      (cotangentChartInv d (cotangentChart d (cotangentChartInv c (p.1, p.2.1)))).1
      (cotangentChartInv d (cotangentChart d (cotangentChartInv c (p.1, p.2.1)))).2 p.2.2 =
    envelopeRaw h T (cotangentChartInv c (p.1, p.2.1)).1
      (cotangentChartInv c (p.1, p.2.1)).2 p.2.2
  rw [hi]

theorem spaceTimeChartChange_continuousAt (c d : M.Carrier)
    (p : ComplexVector n × ComplexVector n × ℝ) (hp : p.1 ∈ chartTarget c)
    (hd : chartInv c p.1 ∈ (extChartAt (ComplexModel n) d).source) :
    ContinuousAt (spaceTimeChartChange c d) p := by
  have hpair : ContinuousAt
      (fun q : ComplexVector n × ComplexVector n × ℝ => (q.1, q.2.1)) p :=
    continuousAt_fst.prodMk continuousAt_snd.fst
  have hc := cotangentChartTransition_contDiffAt c d
    (z := (p.1, p.2.1)) ⟨hp, Set.mem_univ _⟩ hd
  have hcoord : ContinuousAt
      (fun q : ComplexVector n × ComplexVector n × ℝ =>
        cotangentChart d (cotangentChartInv c (q.1, q.2.1))) p :=
    ContinuousAt.comp
      (f := fun q : ComplexVector n × ComplexVector n × ℝ => (q.1, q.2.1))
      (g := fun r : CotangentCoord n => cotangentChart d (cotangentChartInv c r))
      hc.continuousAt hpair
  exact hcoord.fst.prodMk (hcoord.snd.prodMk continuousAt_snd.snd)

theorem envelopeRawChart_change_eventually (h : ℝ → HermitianField M) (T : ℝ)
    (c d : M.Carrier) (p : ComplexVector n × ComplexVector n × ℝ)
    (hp : p.1 ∈ chartTarget c)
    (hd : chartInv c p.1 ∈ (extChartAt (ComplexModel n) d).source) :
    (fun q => envelopeRawChart h T d (spaceTimeChartChange c d q)) =ᶠ[𝓝 p]
      envelopeRawChart h T c := by
  have hcis : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (chartInv c) p.1 :=
    ((contMDiffOn_extChartAt_symm (I := ComplexModel n) c).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hp))
  have hci : ContinuousAt (chartInv c) p.1 := hcis.continuousAt
  have hnear : ∀ᶠ q : ComplexVector n × ComplexVector n × ℝ in 𝓝 p,
      chartInv c q.1 ∈ (extChartAt (ComplexModel n) d).source :=
    (hci.comp continuousAt_fst).eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) d).mem_nhds hd)
  filter_upwards [hnear] with q hq
  exact envelopeRawChart_change h T c d q hq

end Yau.NodeProofs.E03Aux
