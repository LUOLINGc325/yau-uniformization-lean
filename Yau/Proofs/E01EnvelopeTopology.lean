import Yau.Proofs.V03Envelope

/-! The actual chart-envelope LSC restricted to fibers and the original valid space/time parameters. -/

noncomputable section
open scoped Topology
open Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem envelopeChart_fiber_lowerSemicontinuous
    (h : ℝ → HermitianField M) (T : ℝ) (x : M.Carrier) (z : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T) :
    LowerSemicontinuous (fun η : ComplexVector n => envelopeChart h T x (z, η, t)) := by
  have hc : Continuous (fun η : ComplexVector n => (z, η, t)) := by fun_prop
  have hm : Set.MapsTo (fun η : ComplexVector n => (z, η, t)) Set.univ
      {p | p.1 ∈ chartTarget x ∧ 0 < p.2.2 ∧ p.2.2 < T} := fun _ _ => ⟨hz, ht⟩
  have henv : LowerSemicontinuousOn (envelopeChart h T x)
      {p | p.1 ∈ chartTarget x ∧ 0 < p.2.2 ∧ p.2.2 < T} :=
    lowerSemicontinuousOn_liminf_nhdsWithin (envelopeRawChart h T x) _
  have hcomp := henv.comp hc.continuousOn hm
  simpa only [Function.comp_def] using lowerSemicontinuousOn_univ_iff.mp hcomp

theorem envelopeChart_validParameters_lowerSemicontinuous
    (h : ℝ → HermitianField M) (T : ℝ) (x : M.Carrier) :
    LowerSemicontinuous (fun q : {p : ComplexVector n × ℝ // p ∈ chartTarget x ×ˢ Ioo 0 T} × ComplexVector n =>
      envelopeChart h T x (q.1.val.1, q.2, q.1.val.2)) := by
  have hc : Continuous (fun q : {p : ComplexVector n × ℝ // p ∈ chartTarget x ×ˢ Ioo 0 T} × ComplexVector n =>
      (q.1.val.1, q.2, q.1.val.2)) := by fun_prop
  have hm : Set.MapsTo
      (fun q : {p : ComplexVector n × ℝ // p ∈ chartTarget x ×ˢ Ioo 0 T} × ComplexVector n =>
        (q.1.val.1, q.2, q.1.val.2)) Set.univ
      {p | p.1 ∈ chartTarget x ∧ 0 < p.2.2 ∧ p.2.2 < T} := by
    intro q _
    exact ⟨q.1.property.1, q.1.property.2⟩
  have henv : LowerSemicontinuousOn (envelopeChart h T x)
      {p | p.1 ∈ chartTarget x ∧ 0 < p.2.2 ∧ p.2.2 < T} :=
    lowerSemicontinuousOn_liminf_nhdsWithin (envelopeRawChart h T x) _
  have hcomp := henv.comp hc.continuousOn hm
  simpa only [Function.comp_def] using lowerSemicontinuousOn_univ_iff.mp hcomp

end Yau.NodeProofs.E01Aux
