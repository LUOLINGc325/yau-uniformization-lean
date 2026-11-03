import Yau.Proofs.P06CylinderRegularityEnergy
import Yau.Proofs.P06CylinderRegularityProlongationHeat

/-! The signs and factor of the actual -H/2 equation in value-flux form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.LeafProofs.L16Aux

variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

def heatPrincipal (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ) (p : Point n) : Mat n :=
  fun i j => q i j p / 2

def heatFluxCoeff (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) :
    α → α → Yau.RIdx n → Point n → ℝ :=
  fun r c i p => -(regularityScalarBeta (fun j => (Yau.realVec j,0)) q e1 r c i p)/2

def heatSourceCoeff (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ) :
    α → α → Point n → ℝ := fun r c p =>
  ((∑ i, regularityDirection (Yau.realVec i,0)
    (regularityScalarBeta (fun j => (Yau.realVec j,0)) q e1 r c i) p) - e0 r c p)/2

theorem systemFlux_heat_eq
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (U : Point n → α → ℝ)
    (r : α) (p : Point n) (i : Yau.RIdx n) :
    systemFlux (heatPrincipal q) (heatFluxCoeff q e1) U r p i =
      ((∑ j, q i j p * spatialGradient (fun s => U s r) p j) -
        ∑ c, regularityScalarBeta (fun j => (Yau.realVec j,0)) q e1 r c i p * U p c)/2 := by
  simp only [systemFlux, heatPrincipal, heatFluxCoeff, energyFlux, valueFlux]
  simp only [div_mul_eq_mul_div, neg_div, neg_mul, Finset.sum_neg_distrib,
    ← Finset.sum_div]
  ring

theorem heat_valueFlux_identity
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (U : Point n → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (hU : ∀ c, ContDiff ℝ ∞ (fun p => U p c)) (p : Point n) (r : α) :
    (∑ i, fderiv ℝ (fun s => systemFlux (heatPrincipal q) (heatFluxCoeff q e1) U r s i)
      p (Yau.realVec i,0)) + valueSource (heatSourceCoeff q e1 e0) U r p =
      -(systemOperator (fun i => (Yau.realVec i,0)) q e1 e0 U p r)/2 := by
  let v : Yau.RIdx n → Point n := fun i => (Yau.realVec i,0)
  let β := regularityScalarBeta v q e1
  have hβ : ∀ r c i, ContDiff ℝ ∞ (β r c i) :=
    regularityScalarBeta_contDiff v q e1 hq he1
  have hnondiv := regularityScalarSystem_nondivergence v q e1 e0 U hq he1 hU p r
  change regularityScalarSystem v q β e0 U p r = systemOperator v q e1 e0 U p r at hnondiv
  have hFlux (i : Yau.RIdx n) :
      fderiv ℝ (fun s => systemFlux (heatPrincipal q) (heatFluxCoeff q e1) U r s i)
        p (v i) =
      ((∑ j, regularityDirection (v i)
        (fun s => q i j s * regularityDirection (v j) (fun y => U y r) s) p) -
        ∑ c, (regularityDirection (v i) (β r c i) p * U p c +
          β r c i p * regularityDirection (v i) (fun y => U y c) p))/2 := by
    have hA : ContDiff ℝ ∞ (fun s => ∑ j, q i j s *
        spatialGradient (fun y => U y r) s j) :=
      ContDiff.sum fun j _ => (hq i j).mul (regularityDirection_contDiff (hU r) (v j))
    have hB : ContDiff ℝ ∞ (fun s => ∑ c, β r c i s * U s c) :=
      ContDiff.sum fun c _ => (hβ r c i).mul (hU c)
    have hAder : fderiv ℝ (fun s => ∑ j, q i j s * spatialGradient (fun y => U y r) s j)
        p (v i) = ∑ j, regularityDirection (v i)
          (fun s => q i j s * regularityDirection (v j) (fun y => U y r) s) p := by
      change fderiv ℝ (fun s => ∑ j, q i j s * regularityDirection (v j)
        (fun y => U y r) s) p (v i) = _
      rw [fderiv_fun_sum (fun j _ => ((hq i j).mul
        (regularityDirection_contDiff (hU r) (v j))).differentiable (by simp) p)]
      simp only [ContinuousLinearMap.sum_apply, spatialGradient, regularityDirection, v]
    have hBder : fderiv ℝ (fun s => ∑ c, β r c i s * U s c) p (v i) =
        ∑ c, (regularityDirection (v i) (β r c i) p * U p c +
          β r c i p * regularityDirection (v i) (fun y => U y c) p) := by
      rw [fderiv_fun_sum (fun c _ => ((hβ r c i).mul (hU c)).differentiable (by simp) p)]
      simp only [ContinuousLinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro c _
      rw [fderiv_fun_mul ((hβ r c i).differentiable (by simp) p)
        ((hU c).differentiable (by simp) p)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, regularityDirection]
      ring
    have hFun : (fun s => systemFlux (heatPrincipal q) (heatFluxCoeff q e1) U r s i) =
        fun s => (1/2 : ℝ) * ((∑ j, q i j s * spatialGradient (fun y => U y r) s j) -
          ∑ c, β r c i s * U s c) := by
      funext s
      rw [systemFlux_heat_eq]
      dsimp only [β, v]
      ring
    rw [hFun, fderiv_const_mul ((hA.sub hB).differentiable (by simp) p),
      fderiv_fun_sub (hA.differentiable (by simp) p) (hB.differentiable (by simp) p)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.sub_apply,
      hAder, hBder]
    ring
  change (∑ i, fderiv ℝ (fun s => systemFlux (heatPrincipal q) (heatFluxCoeff q e1) U r s i)
    p (v i)) + valueSource (heatSourceCoeff q e1 e0) U r p = -(systemOperator v q e1 e0 U p r)/2
  simp_rw [hFlux]
  rw [← hnondiv]
  simp only [regularityScalarSystem, regularityScalarDiv, valueSource, heatSourceCoeff,
    Finset.sum_add_distrib, sub_div, add_div, div_mul_eq_mul_div, sub_mul,
    Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_mul]
  have hSwap : (∑ i, ∑ c, β r c i p * regularityDirection (v i) (fun y => U y c) p) =
      ∑ c, ∑ i, β r c i p * regularityDirection (v i) (fun y => U y c) p := Finset.sum_comm
  have hSwap' : (∑ i, ∑ c, regularityDirection (v i) (β r c i) p * U p c) =
      ∑ c, ∑ i, regularityDirection (v i) (β r c i) p * U p c := Finset.sum_comm
  change _ = _
  dsimp only [β, v] at hSwap hSwap'
  rw [hSwap, hSwap']
  dsimp only [β, v]
  ring

end Yau.NodeProofs.P06Aux.CylinderReg
