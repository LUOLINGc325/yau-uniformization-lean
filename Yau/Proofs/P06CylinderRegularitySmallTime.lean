import Yau.Proofs.P06CylinderRegularityCompactCoordinates
import Yau.Proofs.P06CylinderRegularitySpatialLocalL2
import Yau.Proofs.P06CylinderRegularityWeightedJets
import Yau.Proofs.P06CylinderRegularityCutoffGerm
import Yau.Proofs.P06SmallTimeCylinder

/-! The explicit small-time cylinder bound for the actual original
Hodge heat, controlled only by a fixed physical compact L² restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03 Yau.LeafProofs.L16Aux

theorem exists_small_time_form_jet_constant {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {O K : Set (ComplexVector n)} (hO : IsOpen O)
    (hcO : IsCompact (closure O)) (hOChart : closure O ⊆ chartTarget x)
    (hK : IsCompact K) (hKO : K ⊆ O) (I : Fin k → RIdx n) (m : ℕ) :
    ∃ (F : Set M.Carrier) (hF : IsCompact F) (C : ℝ), 0 < C ∧ chartInv x '' K ⊆ F ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ U : ℝ → RealForm M k, SmoothFormTime U (Set.Ioi 0) → FormHeatEquation g.form U →
      ∀ hL2 : ∀ s ∈ Set.Ioo (τ/4) (2*τ), L2RealForm g.form μ (U s),
      ∀ L : ℝ, 0 ≤ L →
      (∀ s (hs : s ∈ Set.Ioo (τ/4) (2*τ)),
        ‖Davies.indicator g μ F hF.isClosed.measurableSet (realizeActualForm g μ (U s) (hL2 s hs))‖ ≤ L) →
      ∀ z ∈ K, ∀ t ∈ Set.Icc (τ/2) (3*τ/2),
      ‖iteratedFDeriv ℝ m (fun p : Point n => formComponents (U p.2) x p.1 I) (z,t)‖ ≤
        (C / τ^(3*(m+2*n+1))) * L := by
  classical
  let b := Module.finBasis ℝ (HodgeJets.Fiber n k)
  let Q0 : Set (Point n) := O ×ˢ Set.Ioo (0 : ℝ) 2
  have hCl0 : closure Q0 ⊆ closure O ×ˢ Set.Icc (0 : ℝ) 2 :=
    closure_minimal (fun p hp => ⟨subset_closure hp.1,hp.2.1.le,hp.2.2.le⟩)
      (isClosed_closure.prod isClosed_Icc)
  have hcQ0 : IsCompact (closure Q0) :=
    (hcO.prod isCompact_Icc).of_isClosed_subset isClosed_closure hCl0
  obtain ⟨q,e1,e0,lam,upper,A,hlam,hA,hq,he1,he0,hEll,ha,hqEq,he1Eq,he0Eq⟩ :=
    exists_chart_heat_coefficients g x b hcQ0 (fun p hp => hOChart (hCl0 hp).1)
  obtain ⟨φ,hφ,hcφ,hφO,_,hφone⟩ := exists_model_chart_cutoff
    (isOpen_extChartAt_target (I := ComplexModel n) x) hcO hOChart
  have hone : ∀ z ∈ O, φ z=1 := fun z hz => (hφone z (subset_closure hz)).1
  obtain ⟨D,hD,hLP⟩ := exists_chart_spatial_energy_constant g μ hμ x b φ hφ hcφ hφO O hO.measurableSet hone
  choose C hC hEst using fun r => SmallTimeCylinder.exists_small_time_cylinder_norm_constant q e1 e0
    (fun i j => (hq i j).1) (fun i j => (hq i j).2)
    (fun r c i => (he1 r c i).1) (fun r c i => (he1 r c i).2)
    (fun r c => (he0 r c).1) (fun r c => (he0 r c).2)
    hO hcO hK hKO lam upper A hlam hA hEll ha r m
  let ℓ := fun r => (b r) (fun j => realVec (I j))
  let S := ∑ r, |ℓ r| * C r
  have hS : 0 ≤ S := Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (hC r).le
  let F := CylinderChartL2.physicalSupport x φ
  have hF : IsCompact F := CylinderChartL2.physicalSupport_isCompact x φ hcφ hφO
  have hKF : chartInv x '' K ⊆ F := physicalSupport_contains_chartInv x φ
    (fun z hz => hone z (hKO hz))
  refine ⟨F,hF,(1+S)*(1+D),by positivity,hKF,?_⟩
  intro τ hτ hτ1 U hU hPDE hL2 L hL hBound z hz t ht
  let Qt : Set (Point n) := O ×ˢ Set.Ioo (τ/4) (2*τ)
  have hClt : closure Qt ⊆ closure O ×ˢ Set.Icc (τ/4) (2*τ) :=
    closure_minimal (fun p hp => ⟨subset_closure hp.1,hp.2.1.le,hp.2.2.le⟩)
      (isClosed_closure.prod isClosed_Icc)
  have hcQt : IsCompact (closure Qt) :=
    (hcO.prod isCompact_Icc).of_isClosed_subset isClosed_closure hClt
  have hClosure : closure Qt ⊆ chartTarget x ×ˢ Set.Ioi 0 := fun p hp =>
    ⟨hOChart (hClt hp).1,(by positivity : 0 < τ/4).trans_le (hClt hp).2.1⟩
  have hQt0 : Qt ⊆ Q0 := fun p hp =>
    ⟨hp.1,by linarith [hp.2.1],by linarith [hp.2.2]⟩
  obtain ⟨W,hW,hcW,hGerm⟩ := exists_compact_hodge_coordinates U hU x b hcQt hClosure
  have hHeat := actual_hodge_heatEquation g μ hμ U hU hPDE x b q e1 e0 W hW
    (fun p hp => hClosure (subset_closure hp)) hGerm
    (fun p hp => hqEq p (hQt0 hp)) (fun p hp => he1Eq p (hQt0 hp)) (fun p hp => he0Eq p (hQt0 hp))
  let Lc := (1+D)*L
  have hLc : 0 ≤ Lc := mul_nonneg (by positivity) hL
  have hSlice : ∀ s ∈ Set.Ioo (τ/4) (2*τ), (∫ w in O, valueSquare W (w,s)) ≤ Lc^2 := by
    intro s hs
    have hEqual : (∫ w in O, valueSquare W (w,s)) =
        ∫ w in O, ∑ r, (hodgeRegularityCoord b (U s) x w r)^2 := by
      apply setIntegral_congr_fun hO.measurableSet
      intro w hw
      apply Finset.sum_congr rfl
      intro r _
      rw [(hGerm (w,s) ⟨hw,hs⟩ r).eq_of_nhds]
    rw [hEqual]
    have hN := pow_le_pow_left₀ (norm_nonneg _) (hBound s hs) 2
    have hLPs := (hLP (U s) (hL2 s hs)).trans (mul_le_mul_of_nonneg_left hN hD.le)
    have hBudget : D ≤ (1+D)^2 := by nlinarith [sq_nonneg D]
    exact hLPs.trans ((mul_le_mul_of_nonneg_right hBudget (sq_nonneg L)).trans_eq (by dsimp [Lc]; ring))
  have hpQt : (z,t) ∈ Qt := ⟨hKO hz,by linarith [ht.1],by linarith [ht.2]⟩
  let P := 3*(m+Fintype.card (ParabolicJointIdx n))
  have hEach (r) : ‖iteratedFDeriv ℝ m (fun p => W p r) (z,t)‖ ≤ C r*((1+D)/τ^P*L) := by
    have h := hEst r τ hτ hτ1 W hW hHeat Lc hLc hSlice (z,t) ⟨hz,ht⟩
    exact h.trans_eq (by dsimp [Lc,P]; ring)
  have h := norm_weighted_iteratedFDeriv_le W hW ℓ C ((1+D)/τ^P*L) m (z,t) hEach
  have hJet := ((weighted_hodge_coordinates_germ U x b W (z,t) (hGerm (z,t) hpQt) I).iteratedFDeriv ℝ m).eq_of_nhds
  change iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r*W p r) (z,t) = _ at hJet
  rw [hJet] at h
  have hNonneg : 0 ≤ (1+D)/τ^P*L := mul_nonneg (div_nonneg (by positivity) (pow_nonneg hτ.le _)) hL
  have hTotal := h.trans (mul_le_mul_of_nonneg_right (show S ≤ 1+S by linarith) hNonneg)
  have hCard : Fintype.card (ParabolicJointIdx n)=2*n+1 := by
    simp [ParabolicJointIdx,RIdx,Nat.mul_comm]
  convert hTotal using 1
  dsimp only [P]
  rw [hCard]
  simp only [Nat.add_assoc]
  ring

end Yau.NodeProofs.P06Aux.CylinderReg
