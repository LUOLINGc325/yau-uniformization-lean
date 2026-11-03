import Yau.Proofs.P06CylinderRegularityHeatFlux
import Yau.Proofs.P06CylinderRegularityCoefficientBounds

/-! The computed heat value-flux coefficients and test derivatives have
finite fixed bounds before any solution is chosen. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic

variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

theorem heatCoefficients_regular
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c)) :
    (∀ r c i, ContDiff ℝ ∞ (heatFluxCoeff q e1 r c i) ∧
      HasCompactSupport (heatFluxCoeff q e1 r c i)) ∧
    ∀ r c, ContDiff ℝ ∞ (heatSourceCoeff q e1 e0 r c) ∧
      HasCompactSupport (heatSourceCoeff q e1 e0 r c) := by
  let v : Yau.RIdx n → Point n := fun i => (Yau.realVec i,0)
  have hβ := regularityScalarBeta_contDiff v q e1 hq he1
  have hcβ := regularityScalarBeta_compact v q e1 hcq hce1
  refine ⟨?_,?_⟩
  · intro r c i
    exact ⟨(hβ r c i).neg.div_const 2,
      (hcβ r c i).comp_left (g := fun s : ℝ => -s/2) (by norm_num)⟩
  · intro r c
    have hS : ContDiff ℝ ∞ (fun p => ∑ i, regularityDirection (v i)
        (regularityScalarBeta v q e1 r c i) p) :=
      ContDiff.sum fun i _ => regularityDirection_contDiff (hβ r c i) (v i)
    have hcS : HasCompactSupport (fun p => ∑ i, regularityDirection (v i)
        (regularityScalarBeta v q e1 r c i) p) :=
      compact_sum _ fun i => (hcβ r c i).fderiv_apply ℝ (v i)
    exact ⟨(hS.sub (he0 r c)).div_const 2,
      (hcS.sub (hce0 r c)).comp_left (g := fun s : ℝ => s/2) (by norm_num)⟩

theorem exists_heatCoefficient_bounds
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c)) :
    ∃ D B : ℝ, 0 ≤ D ∧ 0 ≤ B ∧
      (∀ r c i p, |heatFluxCoeff q e1 r c i p| ≤ D) ∧
      ∀ r c p, |heatSourceCoeff q e1 e0 r c p| ≤ B := by
  have h := heatCoefficients_regular q e1 e0 hq hcq he1 hce1 he0 hce0
  obtain ⟨D,hD,hd⟩ := finite_global_abs_bound
    (fun a : α × α × Yau.RIdx n => heatFluxCoeff q e1 a.1 a.2.1 a.2.2)
    (fun a => (h.1 a.1 a.2.1 a.2.2).1.continuous) (fun a => (h.1 a.1 a.2.1 a.2.2).2)
  obtain ⟨B,hB,hb⟩ := finite_global_abs_bound
    (fun a : α × α => heatSourceCoeff q e1 e0 a.1 a.2)
    (fun a => (h.2 a.1 a.2).1.continuous) (fun a => (h.2 a.1 a.2).2)
  exact ⟨D,B,hD,hB,fun r c i p => hd (r,c,i) p,fun r c p => hb (r,c) p⟩

theorem exists_test_firstDerivative_bound {η : Point n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ p, |fderiv ℝ η p (0,1)| ≤ M) ∧
      ∀ p i, |fderiv ℝ η p (Yau.realVec i,0)| ≤ M := by
  let dir : Option (Yau.RIdx n) → Point n
    | none => (0,1)
    | some i => (Yau.realVec i,0)
  obtain ⟨M,hM,hb⟩ := finite_global_abs_bound (fun i p => fderiv ℝ η p (dir i))
    (fun i => ((hη.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous)
    (fun i => hcη.fderiv_apply ℝ (dir i))
  exact ⟨M,hM,fun p => hb none p,fun p i => hb (some i) p⟩

end Yau.NodeProofs.P06Aux.CylinderReg
