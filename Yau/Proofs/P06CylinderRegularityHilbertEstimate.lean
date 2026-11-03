import Yau.Proofs.P06CylinderRegularityFormEstimate
import Yau.Proofs.P06CylinderRegularityTimeEnergy
import Yau.LeafProofs.L03RawChartForms

/-! A fixed physical compact Hilbert restriction controls every finite
joint jet of the actual original form heat solution on an inner cylinder. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem exists_local_Hilbert_jet_constant {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {O K : Set (ComplexVector n)} (hO : IsOpen O)
    (hcO : IsCompact (closure O)) (hOChart : closure O ⊆ chartTarget x)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (a eps T btime : ℝ) (ha : 0 < a) (haeps : a < eps) (hepsT : eps < T) (hTb : T < btime)
    (I : Fin k → RIdx n) (m : ℕ) :
    ∃ (F : Set M.Carrier) (hF : IsCompact F) (C : ℝ), 0 < C ∧
      ∀ U : ℝ → RealForm M k, SmoothFormTime U (Set.Ioi 0) → FormHeatEquation g.form U →
      ∀ hL2 : ∀ t ∈ Set.Ioo a btime, L2RealForm g.form μ (U t),
      ∀ L : ℝ, 0 ≤ L →
      (∀ t (ht : t ∈ Set.Ioo a btime),
        ‖Davies.indicator g μ F hF.isClosed.measurableSet
          (realizeActualForm g μ (U t) (hL2 t ht))‖ ≤ L) →
      ∀ z ∈ K, ∀ t ∈ Set.Icc eps T,
      ‖iteratedFDeriv ℝ m (fun p : Point n => formComponents (U p.2) x p.1 I) (z,t)‖ ≤ C*L := by
  classical
  have hab : a < btime := haeps.trans (hepsT.trans hTb)
  let b := Module.finBasis ℝ (HodgeJets.Fiber n k)
  obtain ⟨φ,hφ,hcφ,hφO,_,hφone⟩ := exists_model_chart_cutoff
    (isOpen_extChartAt_target (I := ComplexModel n) x) hcO hOChart
  have hone : ∀ z ∈ O, φ z = 1 := fun z hz => (hφone z (subset_closure hz)).1
  let Q : Set (Point n) := O ×ˢ Set.Ioo a btime
  have hQ : IsOpen Q := hO.prod isOpen_Ioo
  have hClSub : closure Q ⊆ closure O ×ˢ Set.Icc a btime :=
    closure_minimal (fun p hp => ⟨subset_closure hp.1, hp.2.1.le, hp.2.2.le⟩)
      (isClosed_closure.prod isClosed_Icc)
  have hcQ : IsCompact (closure Q) :=
    (hcO.prod isCompact_Icc).of_isClosed_subset isClosed_closure hClSub
  have hClPos : closure Q ⊆ chartTarget x ×ˢ Set.Ioi 0 := fun p hp =>
    ⟨hOChart (hClSub hp).1, ha.trans_le (hClSub hp).2.1⟩
  have hKQ : K ×ˢ Set.Icc eps T ⊆ Q := fun p hp =>
    ⟨hKO hp.1, haeps.trans_le hp.2.1, hp.2.2.trans_lt hTb⟩
  obtain ⟨C1,hC1,hJet⟩ := exists_local_form_jet_constant g μ hμ x b hQ hcQ hClPos
    (hK.prod isCompact_Icc) hKQ I m
  obtain ⟨C2,hC2,hEnergy⟩ := exists_chart_time_energy_constant g μ hμ x b φ hφ hcφ hφO
    O hO.measurableSet hone a btime hab
  let F := CylinderChartL2.physicalSupport x φ
  have hF : IsCompact F := CylinderChartL2.physicalSupport_isCompact x φ hcφ hφO
  refine ⟨F,hF,1+C1*C2,by positivity,?_⟩
  intro U hU hPDE hL2 L hL hBound z hz t ht
  have hE := hEnergy U (chartValue_integrableOn U hU x b hcQ hClPos) hL2 L hL hBound
  have hJ := hJet U hU hPDE (z,t) ⟨hz,ht⟩
  have hTotal := hJ.trans (mul_le_mul_of_nonneg_left hE hC1.le)
  have hBudget : C1*C2 ≤ (1+C1*C2)^2 := by nlinarith [sq_nonneg (C1*C2)]
  have hSq : ‖iteratedFDeriv ℝ m (fun p : Point n => formComponents (U p.2) x p.1 I) (z,t)‖^2 ≤
      ((1+C1*C2)*L)^2 := by
    calc
      _ ≤ C1*C2*L^2 := by nlinarith only [hTotal]
      _ ≤ (1+C1*C2)^2*L^2 := mul_le_mul_of_nonneg_right hBudget (sq_nonneg L)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity : 0 ≤ 1+C1*C2) hL)).mp hSq

end Yau.NodeProofs.P06Aux.CylinderReg
