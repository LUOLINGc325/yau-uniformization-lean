import Yau.Proofs.E03RawChartChange
import Yau.Proofs.E03LiminfTransport

/-! SOURCE-ONLY E03 candidate: transport the original neighborhood liminf at valid interior time. -/

noncomputable section
open scoped Manifold Topology ContDiff
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem spaceTimeChartChange_inverse (c d : M.Carrier)
    (p : ComplexVector n × ComplexVector n × ℝ) (hp : p.1 ∈ chartTarget c)
    (hd : chartInv c p.1 ∈ (extChartAt (ComplexModel n) d).source) :
    spaceTimeChartChange d c (spaceTimeChartChange c d p) = p := by
  have hdi := cotangentChart_left_inv d (y := cotangentChartInv c (p.1, p.2.1)) hd
  have hci := cotangentChart_right_inv c (z := (p.1, p.2.1)) ⟨hp, Set.mem_univ _⟩
  change
    ((cotangentChart c (cotangentChartInv d
        (cotangentChart d (cotangentChartInv c (p.1, p.2.1))))).1,
      (cotangentChart c (cotangentChartInv d
        (cotangentChart d (cotangentChartInv c (p.1, p.2.1))))).2, p.2.2) = p
  rw [hdi, hci]

theorem envelopeChart_eq_liminf_nhds (h : ℝ → HermitianField M) (T : ℝ)
    (c : M.Carrier) (p : ComplexVector n × ComplexVector n × ℝ)
    (hp : p.1 ∈ chartTarget c) (ht : p.2.2 ∈ Ioo 0 T) :
    envelopeChart h T c p = liminf (envelopeRawChart h T c) (𝓝 p) := by
  let S : Set (ComplexVector n × ComplexVector n × ℝ) :=
    {q | q.1 ∈ chartTarget c ∧ 0 < q.2.2 ∧ q.2.2 < T}
  have hbase : IsOpen {q : ComplexVector n × ComplexVector n × ℝ | q.1 ∈ chartTarget c} :=
    (isOpen_extChartAt_target (I := ComplexModel n) c).preimage continuous_fst
  have hc : Continuous (fun q : ComplexVector n × ComplexVector n × ℝ => q.2.2) :=
    continuous_snd.comp continuous_snd
  have hS : IsOpen S := hbase.inter (isOpen_Ioo.preimage hc)
  change liminf (envelopeRawChart h T c) (𝓝[S] p) = _
  rw [nhdsWithin_eq_nhds.mpr (hS.mem_nhds ⟨hp, ht⟩)]

theorem envelopeChart_chartChange (h : ℝ → HermitianField M) (T : ℝ)
    (c d : M.Carrier) (p : ComplexVector n × ComplexVector n × ℝ)
    (hp : p.1 ∈ chartTarget c)
    (hd : chartInv c p.1 ∈ (extChartAt (ComplexModel n) d).source)
    (ht : p.2.2 ∈ Ioo 0 T) :
    envelopeChart h T d (spaceTimeChartChange c d p) = envelopeChart h T c p := by
  let q := spaceTimeChartChange c d p
  have hqd : q.1 ∈ chartTarget d := (extChartAt (ComplexModel n) d).map_source hd
  have hbase : chartInv d q.1 = chartInv c p.1 :=
    (extChartAt (ComplexModel n) d).left_inv hd
  have hback : chartInv d q.1 ∈ (extChartAt (ComplexModel n) c).source := by
    rw [hbase]
    exact (extChartAt (ComplexModel n) c).map_target hp
  have hround : spaceTimeChartChange d c q = p := spaceTimeChartChange_inverse c d p hp hd
  have he : Tendsto (spaceTimeChartChange c d) (𝓝 p) (𝓝 q) :=
    (spaceTimeChartChange_continuousAt c d p hp hd).tendsto
  have hi : Tendsto (spaceTimeChartChange d c) (𝓝 q) (𝓝 p) := by
    simpa only [hround] using (spaceTimeChartChange_continuousAt d c q hqd hback).tendsto
  have hl := liminf_eq_of_two_continuous_germ_transports
    (envelopeRawChart h T c) (envelopeRawChart h T d) p q
    (spaceTimeChartChange c d) (spaceTimeChartChange d c) he hi
    (envelopeRawChart_change_eventually h T c d p hp hd)
    (envelopeRawChart_change_eventually h T d c q hqd hback)
  have hqt : q.2.2 ∈ Ioo 0 T := ht
  rw [envelopeChart_eq_liminf_nhds h T d q hqd hqt,
    envelopeChart_eq_liminf_nhds h T c p hp ht]
  exact hl.symm

end Yau.NodeProofs.E03Aux
