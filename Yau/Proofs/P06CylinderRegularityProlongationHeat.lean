import Yau.Proofs.P06CylinderRegularityProlongation
import Yau.Blueprint.ParabolicSpaces

/-! The actual heat clock -1/2 is retained under finite classical
prolongation. The equation is differentiated only inside its open domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic

variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

def heatEquation (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (Q : Set (Point n)) (U : Point n → α → ℝ) : Prop :=
  ∀ p ∈ Q, ∀ r, fderiv ℝ (fun s => U s r) p (0,1) =
    -(systemOperator (fun i => (Yau.realVec i,0)) q e1 e0 U p r)/2

theorem prolongValue_contDiff {U : Point n → α → ℝ}
    (hU : ∀ c, ContDiff ℝ ∞ (fun p => U p c)) (r : RegularityProlongIndex α (Yau.RIdx n)) :
    ContDiff ℝ ∞ (fun p => regularityProlongValue (fun i => (Yau.realVec i,0)) U p r) := by
  rcases r with ⟨r,s⟩
  cases s with
  | none => exact hU r
  | some i => exact regularityDirection_contDiff (hU r) (Yau.realVec i,0)

theorem heatEquation_prolong
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    {Q : Set (Point n)} (hQ : IsOpen Q) (U : Point n → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun p => U p c))
    (hPDE : heatEquation q e1 e0 Q U) :
    heatEquation q
      (regularityProlongE1 (fun i => (Yau.realVec i,0)) q e1)
      (regularityProlongE0 (fun i => (Yau.realVec i,0)) e1 e0) Q
      (regularityProlongValue (fun i => (Yau.realVec i,0)) U) := by
  intro p hp r
  rcases r with ⟨r,s⟩
  cases s with
  | none =>
    rw [systemOperator_prolong_none]
    exact hPDE p hp r
  | some ell =>
    rw [systemOperator_prolong_some _ _ _ _ _ hq he1 he0 hU]
    have hg : (fun z => fderiv ℝ (fun s => U s r) z (0,1)) =ᶠ[𝓝 p]
        (fun z => -(systemOperator (fun i => (Yau.realVec i,0)) q e1 e0 U z r)/2) := by
      filter_upwards [hQ.mem_nhds hp] with z hz
      exact hPDE z hz r
    have hd := congrArg (fun L : Point n →L[ℝ] ℝ => L (Yau.realVec ell,0))
      hg.fderiv.eq_of_nhds
    have hOp := (systemOperator_contDiff (fun i => (Yau.realVec i,0)) q e1 e0 U
      hq he1 he0 hU r).differentiable (by simp) p
    have hcomm := congrFun (regularityDirection_commute (hU r) (0,1) (Yau.realVec ell,0)) p
    change fderiv ℝ (fun z => fderiv ℝ (fun s => U s r) z (Yau.realVec ell,0)) p (0,1) = _
    change fderiv ℝ (fun z => fderiv ℝ (fun s => U s r) z (Yau.realVec ell,0)) p (0,1) =
      fderiv ℝ (fun z => fderiv ℝ (fun s => U s r) z (0,1)) p (Yau.realVec ell,0) at hcomm
    rw [hcomm]
    rw [hd]
    have hFun : (fun z => -(systemOperator (fun i => (Yau.realVec i,0)) q e1 e0 U z r)/2) =
        fun z => (-(1/2 : ℝ))*systemOperator (fun i => (Yau.realVec i,0)) q e1 e0 U z r := by
      funext z
      ring
    rw [hFun, fderiv_const_mul hOp]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, regularityDirection]
    ring

end Yau.NodeProofs.P06Aux.CylinderReg
