import Yau.Proofs.E02JointDualNorm
import Yau.Proofs.E02FiniteEReal
import Yau.Proofs.E01RawUpper
import Yau.Proofs.V03Envelope

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

variable {n : ℕ} (X : KahlerManifold n)

def chartEnvelopeReal (h : Flow X) (T : ℝ) (x : Pt X)
    (p : ComplexVector n × ComplexVector n × ℝ) : ℝ := (envelopeChart h T x p).toReal

theorem envelopeChart_bounds (h : Flow X) (T : ℝ) (x : Pt X)
    (p : ComplexVector n × ComplexVector n × ℝ) (hp : p ∈ envelopeDomain X T x) :
    0 ≤ envelopeChart h T x p ∧
      envelopeChart h T x p ≤ (dualNormChart (h p.2.2) x p.1 p.2.1 : EReal) := by
  refine ⟨V03Proof.envelopeChart_nonneg h T x p,?_⟩
  apply (V03Proof.envelopeChart_le_raw h T x p hp).trans
  have he := V03Proof.dualNorm_cotangentChartInv (h p.2.2) x
    (z := (p.1,p.2.1)) ⟨hp.1,mem_univ _⟩
  change dualNorm (h p.2.2) (chartInv x p.1)
    (covectorOfCoords x (chartInv x p.1) p.2.1) = _ at he
  change envelopeRaw h T (chartInv x p.1)
    (covectorOfCoords x (chartInv x p.1) p.2.1) p.2.2 ≤ _
  rw [←he]
  exact E01Aux.envelopeRaw_le_actual_dualNorm h T _ _ p.2.2 hp.2.1 hp.2.2

/-- The original envelope is finite before applying toReal. -/
theorem chartEnvelopeReal_finite_bounds (h : Flow X) (T : ℝ) (x : Pt X)
    (p : ComplexVector n × ComplexVector n × ℝ) (hp : p ∈ envelopeDomain X T x) :
    envelopeChart h T x p ≠ ⊤ ∧ envelopeChart h T x p ≠ ⊥ ∧
      (chartEnvelopeReal X h T x p : EReal) = envelopeChart h T x p ∧
      0 ≤ chartEnvelopeReal X h T x p ∧
      chartEnvelopeReal X h T x p ≤ dualNormChart (h p.2.2) x p.1 p.2.1 := by
  obtain ⟨h0,hUp⟩ := envelopeChart_bounds X h T x p hp
  exact nonnegative_ereal_finite_bounds _ _ h0 hUp

theorem chartEnvelopeReal_lowerSemicontinuousOn (h : Flow X) (T : ℝ) (x : Pt X) :
    LowerSemicontinuousOn (chartEnvelopeReal X h T x) (envelopeDomain X T x) := by
  exact lowerSemicontinuousOn_ereal_toReal (envelopeChart h T x) (envelopeDomain X T x)
    (V03Proof.envelopeChart_lowerSemicontinuousOn h T x)
    (fun p hp => (chartEnvelopeReal_finite_bounds X h T x p hp).1)
    (fun p hp => (chartEnvelopeReal_finite_bounds X h T x p hp).2.1)

/-- A single compact metric bound controls this same real envelope before
any regularization or contact selection. -/
theorem chartEnvelopeReal_compact_bounds (h : Flow X)
    (hh : MetricFamilySmooth h (Ici 0)) (T : ℝ) (x : Pt X)
    (K : Set (ComplexVector n × ComplexVector n × ℝ))
    (hK : IsCompact K) (hDom : K ⊆ envelopeDomain X T x) :
    ∃ M : ℝ, 0 < M ∧ ∀ p ∈ K, 0 ≤ chartEnvelopeReal X h T x p ∧
      chartEnvelopeReal X h T x p ≤ M := by
  obtain ⟨M,hM,hUpper⟩ := jointDualNorm_compact_upper X h hh T x K hK hDom
  refine ⟨M,hM,?_⟩
  intro p hp
  have hb := (chartEnvelopeReal_finite_bounds X h T x p (hDom hp)).2.2.2
  exact ⟨hb.1,hb.2.trans (hUpper p hp)⟩

end Yau.NodeProofs.E02Aux
