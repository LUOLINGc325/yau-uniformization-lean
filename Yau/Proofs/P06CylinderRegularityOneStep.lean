import Yau.Proofs.P06CylinderRegularitySpatialEnergy
import Yau.Proofs.P06CylinderRegularityHeatBounds

/-! One fully discharged local energy step for the actual heat operator,
with constants selected before the smooth solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_one_step_energy_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {Q K : Set (Point n)} (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : Elliptic Q (heatPrincipal q) lam upper)
    (ha : ∀ p ∈ Q, ∀ i j, |heatPrincipal q p i j| ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 Q U → IntegrableOn (valueSquare U) Q →
      (∫ p in K, valueSquare (regularityProlongValue (fun i => (Yau.realVec i,0)) U) p) ≤
        C * ∫ p in Q, valueSquare U p := by
  obtain ⟨η,hη,hηB,hηNear⟩ := exists_bounded_test_eq_one_near_compact hQ hK hKQ
  obtain ⟨ζ,hζ,hζB,hζNear⟩ := exists_bounded_test_eq_one_near_compact hQ hη.2.1 hη.2.2
  obtain ⟨M,hM,hTime,hSpace⟩ := exists_test_firstDerivative_bound hη.1 hη.2.1
  obtain ⟨D,B,hD,hB,hd,he⟩ := exists_heatCoefficient_bounds q e1 e0 hq hcq he1 hce1 he0 hce0
  have hCoeff := heatCoefficients_regular q e1 e0 hq hcq he1 hce1 he0 hce0
  obtain ⟨C,hC,hEst⟩ := exists_local_system_gradient_constant n α lam upper A D B M hlam hA hD hB hM
  refine ⟨1+C,by positivity,?_⟩
  intro U hU hPDE hUI
  have hFluxPDE : ∀ p ∈ Q, ∀ r, fderiv ℝ (fun s => U s r) p (0,1) =
      (∑ i, fderiv ℝ (fun s => systemFlux (heatPrincipal q) (heatFluxCoeff q e1) U r s i)
        p (Yau.realVec i,0)) + valueSource (heatSourceCoeff q e1 e0) U r p := by
    intro p hp r
    rw [heat_valueFlux_identity q e1 e0 U hq he1 hU p r]
    exact hPDE p hp r
  have hGrad := hEst Q (heatPrincipal q) (heatFluxCoeff q e1) (heatSourceCoeff q e1 e0) η ζ U
    hQ hEll ha (fun i j => (hq i j).div_const 2)
    (fun r c i => (hCoeff.1 r c i).1) (fun r c => (hCoeff.2 r c).1)
    hd he hη hζ hηB hζB hζNear hTime hSpace (fun r => (hU r).contDiffOn) hUI hFluxPDE
  have hηone : ∀ p ∈ K, η p = 1 := fun p hp => (hηNear p hp).eq_of_nhds
  have hInner := inner_gradient_energy_le hQ hK.measurableSet hη hηone
    (fun r => (hU r).contDiffOn)
  have hGradBound : (∫ p in K, gradientSquare U p) ≤ C * ∫ p in Q, valueSquare U p :=
    hInner.trans hGrad
  have hValueBound := integral_valueSquare_mono hKQ hUI
  have hG : ContDiff ℝ ∞ (gradientSquare U) :=
    ContDiff.sum fun r _ => ContDiff.sum fun i _ => (gradient_contDiff (hU r) i).pow 2
  have hGI : IntegrableOn (gradientSquare U) K := hG.continuous.continuousOn.integrableOn_compact hK
  have hVI : IntegrableOn (valueSquare U) K := hUI.mono_set hKQ
  simp_rw [prolong_valueSquare]
  rw [integral_add hVI hGI]
  nlinarith

end Yau.NodeProofs.P06Aux.CylinderReg
