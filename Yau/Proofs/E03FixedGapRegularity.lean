import Yau.Proofs.E03GlobalGap

/-! Smooth fixed-chart log-cometric and upper semicontinuity of the original scalar gap. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem negative_logDet_contDiffOn (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (c : Pt X) (T : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => -logDet (h p.2) c p.1)
      (chartTarget c ×ˢ Ioo 0 T) := by
  have hρ : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => ρ (chartInv c p.1) p.2)
      (chartTarget c ×ˢ Ioo 0 T) :=
    (hloc.2.2.2.1 c).mono (fun p hp => ⟨hp.1, hp.2.1.le⟩)
  have hproj : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => p.1)
      (chartTarget c ×ˢ Ioo 0 T) := contDiff_fst.contDiffOn
  have hg : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => logDet X.metric.form c p.1)
      (chartTarget c ×ˢ Ioo 0 T) :=
    (Yau.LeafProofs.L12Aux.logDet_contDiffOn X.metric c).comp hproj (fun p hp => hp.1)
  apply (hρ.sub hg).congr
  intro p hp
  have hr := Yau.F04Proof.rho_in_fixed_chart o h U P ρ hloc c p.2 hp.2.1.le p.1 hp.1
  linarith

theorem volumeGap_upperSemicontinuousOn (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (c : Pt X) (T : ℝ) (hT : 0 < T) :
    UpperSemicontinuousOn (fun p : ComplexVector n × ℝ => volumeGap X h T c p.1 p.2)
      (chartTarget c ×ˢ Ioo 0 T) := by
  have hell := (negative_logDet_contDiffOn o h U P ρ hloc c T).continuousOn.upperSemicontinuousOn
  have hneg := (hopt T hT c).1.neg
  have ha := hell.add hneg
  simpa only [volumeGap, sub_eq_add_neg, Pi.neg_apply] using ha

end Yau.NodeProofs.E03Aux
