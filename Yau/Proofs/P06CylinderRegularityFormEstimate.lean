import Yau.Proofs.P06CylinderRegularityChartData
import Yau.Proofs.P06CylinderRegularityLinearJets

/-! The local value-L² to full cylinder-jet estimate for actual smooth
solutions of the original form heat equation, in every degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03 Yau.LeafProofs.L16Aux

theorem form_component_basis_expansion {n k : ℕ} {M : ComplexManifold n}
    {α : Type} [Fintype α] (b : Basis α ℝ (HodgeJets.Fiber n k))
    (A : RealForm M k) (x : M.Carrier) (z : ComplexVector n) (I : Fin k → RIdx n) :
    (∑ r, (b r) (fun j => realVec (I j)) * hodgeRegularityCoord b A x z r) =
      formComponents A x z I := by
  have h := congrArg (fun P : HodgeJets.Fiber n k => P (fun j => realVec (I j)))
    (b.sum_repr (chartForm A x z))
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, chartForm_apply_basis] at h
  simpa only [hodgeRegularityCoord, mul_comm] using h

theorem exists_local_form_jet_constant {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {α : Type} [Fintype α] [DecidableEq α]
    (b : Basis α ℝ (HodgeJets.Fiber n k))
    {Q K : Set (Point n)} (hQ : IsOpen Q) (hcQ : IsCompact (closure Q))
    (hClosure : closure Q ⊆ chartTarget x ×ˢ Set.Ioi 0)
    (hK : IsCompact K) (hKQ : K ⊆ Q) (I : Fin k → RIdx n) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ → RealForm M k,
      SmoothFormTime U (Set.Ioi 0) → FormHeatEquation g.form U → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (fun p : Point n => formComponents (U p.2) x p.1 I) p‖^2 ≤
        C * ∫ p in Q, valueSquare (fun p r => hodgeRegularityCoord b (U p.2) x p.1 r) p := by
  classical
  obtain ⟨q,e1,e0,lam,upper,A,hlam,hA,hq,he1,he0,hEll,ha,hqEq,he1Eq,he0Eq⟩ :=
    exists_chart_heat_coefficients g x b hcQ (fun p hp => (hClosure hp).1)
  have hO : IsOpen (chartTarget x ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  obtain ⟨ζ,hζ,hζNear⟩ := exists_test_eq_one_near_compact hO hcQ hClosure
  let ℓ : α → ℝ := fun r => (b r) (fun j => realVec (I j))
  obtain ⟨C,hC,hEst⟩ := exists_joint_linear_jet_constant q e1 e0
    (fun i j => (hq i j).1) (fun i j => (hq i j).2)
    (fun r c i => (he1 r c i).1) (fun r c i => (he1 r c i).2)
    (fun r c => (he0 r c).1) (fun r c => (he0 r c).2)
    hQ hK hKQ lam upper A hlam hA hEll ha ℓ m
  refine ⟨C,hC,?_⟩
  intro U hU hPDE p hp
  let W : Point n → α → ℝ := fun p r => ζ p * hodgeRegularityCoord b (U p.2) x p.1 r
  have hW (r : α) : ContDiff ℝ ∞ (fun p => W p r) :=
    (cutoff_contDiff hO hζ.1 hζ.2.1 hζ.2.2 (hodgeCoordinate_joint_contDiffOn U hU x b r)).1
  have hcW (r : α) : HasCompactSupport (fun p => W p r) :=
    (cutoff_contDiff hO hζ.1 hζ.2.1 hζ.2.2 (hodgeCoordinate_joint_contDiffOn U hU x b r)).2
  have hGerm : ∀ p ∈ Q, ∀ r, (fun s => W s r) =ᶠ[𝓝 p]
      (fun s => hodgeRegularityCoord b (U s.2) x s.1 r) := by
    intro p hp r
    exact cutoff_eq_germ (hζNear p (subset_closure hp))
  have hHeat := actual_hodge_heatEquation g μ hμ U hU hPDE x b q e1 e0 W hW
    (fun p hp => hClosure (subset_closure hp)) hGerm hqEq he1Eq he0Eq
  have hBound := hEst W hW hHeat (valueSquare_integrable hW hcW).integrableOn p hp
  have hFunction : (fun p => ∑ r, ℓ r * W p r) =ᶠ[𝓝 p]
      (fun p : Point n => formComponents (U p.2) x p.1 I) := by
    filter_upwards [hζNear p (subset_closure (hKQ hp))] with s hs
    dsimp only [W,ℓ]
    simp only [hs,one_mul]
    exact form_component_basis_expansion b (U s.2) x s.1 I
  have hJet : iteratedFDeriv ℝ m (fun p => ∑ r, ℓ r * W p r) p =
      iteratedFDeriv ℝ m (fun p : Point n => formComponents (U p.2) x p.1 I) p :=
    (hFunction.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
  have hIntegral : (∫ p in Q, valueSquare W p) =
      ∫ p in Q, valueSquare (fun p r => hodgeRegularityCoord b (U p.2) x p.1 r) p := by
    apply setIntegral_congr_fun hQ.measurableSet
    intro s hs
    have hOne : ζ s = 1 := (hζNear s (subset_closure hs)).eq_of_nhds
    simp only [valueSquare,W,hOne,one_mul]
  rw [hJet,hIntegral] at hBound
  exact hBound

end Yau.NodeProofs.P06Aux.CylinderReg
