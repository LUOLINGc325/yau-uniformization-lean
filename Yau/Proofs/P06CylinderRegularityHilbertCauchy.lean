import Yau.Proofs.P06CylinderRegularityHilbertEstimate
import Yau.Proofs.P06CylinderRegularityFormLinear

/-! Actual localized Hilbert Cauchy control implies all original joint
component jets are uniformly Cauchy on every positive compact cylinder. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem localized_Hilbert_Cauchy_form_jets {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (U V : ℕ → ℝ → RealForm M k)
    (hUs : ∀ j, 1 ≤ j → SmoothFormTime (U j) (Set.Ioi 0))
    (hVs : ∀ j, 1 ≤ j → SmoothFormTime (V j) (Set.Ioi 0))
    (hUPDE : ∀ j, 1 ≤ j → FormHeatEquation g.form (U j))
    (hVPDE : ∀ j, 1 ≤ j → FormHeatEquation g.form (V j))
    (hUL : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm g.form μ (U j t))
    (hVL : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm g.form μ (V j t))
    (hCauchy : ∀ (F : Set M.Carrier) (hF : IsCompact F) (T : ℝ), 0 < T →
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, 1 ≤ N ∧
      ∀ j l (hj : 1 ≤ j) (hl : 1 ≤ l), N ≤ j → N ≤ l → ∀ t (ht : 0 < t), t ≤ T →
        ‖Davies.indicator g μ F hF.isClosed.measurableSet
          (realizeActualForm g μ (U j t) (hUL j hj t ht)-
            realizeActualForm g μ (V l t) (hVL l hl t ht))‖ < η) :
    ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ eps T, 0 < eps → eps < T → ∀ (m : ℕ) (I : Fin k → RIdx n) η, 0 < η →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j l, N ≤ j → N ≤ l → ∀ z ∈ K, ∀ t ∈ Set.Icc eps T,
      ‖iteratedFDeriv ℝ m (fun p : Point n =>
        formComponents (U j p.2) x p.1 I-formComponents (V l p.2) x p.1 I) (z,t)‖ < η := by
  intro x K hK hKChart eps T heps hepsT m I η hη
  obtain ⟨O,hO,hKO,hOChart,hcO⟩ := exists_open_between_and_isCompact_closure hK
    (isOpen_extChartAt_target (I := ComplexModel n) x) hKChart
  obtain ⟨F,hF,C,hC,hEst⟩ := exists_local_Hilbert_jet_constant g μ hμ x hO hcO hOChart hK hKO
    (eps/2) eps T (T+eps) (by positivity) (by linarith) hepsT (by linarith) I m
  let δ := η/(C+1)
  have hC1 : 0 < C+1 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hCancel : δ*(C+1)=η := by dsimp [δ]; exact div_mul_cancel₀ _ hC1.ne'
  have hBudget : C*δ < η := by nlinarith only [hδ,hCancel]
  obtain ⟨N,hNpos,hN⟩ := hCauchy F hF (T+eps) (by linarith) δ hδ
  refine ⟨N,hNpos,?_⟩
  intro j l hj hl z hz t ht
  have hj1 : 1 ≤ j := hNpos.trans hj
  have hl1 : 1 ≤ l := hNpos.trans hl
  let D : ℝ → RealForm M k := fun t => U j t-V l t
  let hDL : ∀ s ∈ Set.Ioo (eps/2) (T+eps), L2RealForm g.form μ (D s) := fun s hs =>
    l2RealForm_sub g μ (U j s) (V l s) (hUL j hj1 s (by linarith [hs.1]))
      (hVL l hl1 s (by linarith [hs.1]))
  have hPhys : ∀ s (hs : s ∈ Set.Ioo (eps/2) (T+eps)),
      ‖Davies.indicator g μ F hF.isClosed.measurableSet (realizeActualForm g μ (D s) (hDL s hs))‖ ≤ δ := by
    intro s hs
    have hspos : 0 < s := by linarith [hs.1]
    have h := hN j l hj1 hl1 hj hl s hspos hs.2.le
    rw [realizeActualForm_sub]
    exact h.le
  have h := hEst D (smoothFormTime_sub (hUs j hj1) (hVs l hl1))
    (formHeatEquation_sub g μ hμ (hUs j hj1) (hVs l hl1) (hUPDE j hj1) (hVPDE l hl1))
    hDL δ hδ.le hPhys z hz t ht
  exact h.trans_lt hBudget

end Yau.NodeProofs.P06Aux.CylinderReg
