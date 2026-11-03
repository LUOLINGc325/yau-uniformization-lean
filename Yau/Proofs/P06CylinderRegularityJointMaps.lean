import Yau.Proofs.P06CylinderRegularityHierarchy

/-! Every first joint derivative of the finite spatial jet tuple is a
fixed continuous linear expression in two further spatial jet layers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic

variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

abbrev JetSpace (α : Type) (n s : ℕ) := JetIndex α (Yau.RIdx n) s → ℝ

def jetNoneMap (s : ℕ) : JetSpace α n (s+1) →L[ℝ] JetSpace α n s :=
  ContinuousLinearMap.pi fun r => ContinuousLinearMap.proj (r,none)

def jetValueMap (s : ℕ) : JetSpace α n (s+2) →L[ℝ] JetSpace α n s :=
  (jetNoneMap s).comp (jetNoneMap (s+1))

def jetSpaceMap (s : ℕ) (i : Yau.RIdx n) : JetSpace α n (s+2) →L[ℝ] JetSpace α n s :=
  (ContinuousLinearMap.pi fun r => ContinuousLinearMap.proj (r,some i)).comp (jetNoneMap (s+1))

def jetTimeMap
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (s : ℕ) (p : Point n) : JetSpace α n (s+2) →L[ℝ] JetSpace α n s :=
  ContinuousLinearMap.pi fun r =>
    ((∑ i, ∑ j, (q i j p / 2) • ContinuousLinearMap.proj ((r,some j),some i)) -
      ∑ c, ∑ i, (jetE1 (fun i => (Yau.realVec i,0)) q e1 s r c i p / 2) •
        ContinuousLinearMap.proj ((c,some i),none)) -
      ∑ c, (jetE0 (fun i => (Yau.realVec i,0)) q e1 e0 s r c p / 2) •
        ContinuousLinearMap.proj ((c,none),none)

theorem jetTimeMap_apply
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (s : ℕ) (p : Point n) (f : JetSpace α n (s+2)) (r : JetIndex α (Yau.RIdx n) s) :
    jetTimeMap q e1 e0 s p f r =
      ((∑ i, ∑ j, q i j p / 2 * f ((r,some j),some i)) -
        ∑ c, ∑ i, jetE1 (fun i => (Yau.realVec i,0)) q e1 s r c i p / 2 * f ((c,some i),none)) -
        ∑ c, jetE0 (fun i => (Yau.realVec i,0)) q e1 e0 s r c p / 2 * f ((c,none),none) := by
  simp only [jetTimeMap, ContinuousLinearMap.pi_apply, sub_apply, sum_apply]
  apply congrArg₂ (· - ·)
  · apply congrArg₂ (· - ·)
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rfl
    · apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      rfl
  · apply Finset.sum_congr rfl
    intro c _
    rfl

theorem jetValueMap_apply (U : Point n → α → ℝ) (s : ℕ) (p : Point n) :
    jetValueMap (α := α) s (jetValue (fun i => (Yau.realVec i,0)) U (s+2) p) =
      jetValue (fun i => (Yau.realVec i,0)) U s p := rfl

theorem jetSpaceMap_derivative (U : Point n → α → ℝ)
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (s : ℕ) (p : Point n) (i : Yau.RIdx n) :
    fderiv ℝ (jetValue (fun j => (Yau.realVec j,0)) U s) p (Yau.realVec i,0) =
      jetSpaceMap (α := α) s i (jetValue (fun j => (Yau.realVec j,0)) U (s+2) p) := by
  change fderiv ℝ (fun p r => jetValue (fun j => (Yau.realVec j,0)) U s p r) p
    (Yau.realVec i,0) = _
  rw [fderiv_pi (fun r => (jetValue_contDiff _ hU s r).differentiable (by simp) p)]
  rfl

theorem jetTimeMap_contDiff
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c)) (s : ℕ) :
    ContDiff ℝ ∞ (jetTimeMap q e1 e0 s) := by
  have hC := jetCoefficients_regular (fun i => (Yau.realVec i,0)) q e1 e0 hq hcq he1 hce1 he0 hce0 s
  have hRows : ContDiff ℝ ∞ (fun p r =>
      ((∑ i, ∑ j, (q i j p / 2) • (ContinuousLinearMap.proj ((r,some j),some i) :
        JetSpace α n (s+2) →L[ℝ] ℝ)) -
      ∑ c, ∑ i, (jetE1 (fun i => (Yau.realVec i,0)) q e1 s r c i p / 2) •
        ContinuousLinearMap.proj ((c,some i),none)) -
      ∑ c, (jetE0 (fun i => (Yau.realVec i,0)) q e1 e0 s r c p / 2) •
        ContinuousLinearMap.proj ((c,none),none)) := by
    apply contDiff_pi.mpr
    intro r
    exact ((ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      ((hq i j).div_const 2).smul contDiff_const).sub
      (ContDiff.sum fun c _ => ContDiff.sum fun i _ =>
        ((hC.1 r c i).1.div_const 2).smul contDiff_const)).sub
      (ContDiff.sum fun c _ => ((hC.2 r c).1.div_const 2).smul contDiff_const)
  exact (ContinuousLinearMap.piEquivL ℝ (JetSpace α n (s+2))
    (fun _ : JetIndex α (Yau.RIdx n) s => ℝ)).contDiff.comp hRows

theorem jetTimeMap_derivative
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    {Q : Set (Point n)} (hQ : IsOpen Q) (U : Point n → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (hPDE : heatEquation q e1 e0 Q U)
    (s : ℕ) {p : Point n} (hp : p ∈ Q) :
    fderiv ℝ (jetValue (fun j => (Yau.realVec j,0)) U s) p (0,1) =
      jetTimeMap q e1 e0 s p (jetValue (fun j => (Yau.realVec j,0)) U (s+2) p) := by
  have hP := jetValue_heatEquation q e1 e0 hQ U hq hcq he1 hce1 he0 hce0 hU hPDE s
  change fderiv ℝ (fun p r => jetValue (fun j => (Yau.realVec j,0)) U s p r) p (0,1) = _
  rw [fderiv_pi (fun r => (jetValue_contDiff _ hU s r).differentiable (by simp) p)]
  ext r
  change fderiv ℝ (fun p => jetValue (fun j => (Yau.realVec j,0)) U s p r) p (0,1) = _
  rw [hP p hp r]
  rw [jetTimeMap_apply]
  have hSecond (i j : Yau.RIdx n) : jetValue (fun i => (Yau.realVec i,0)) U (s+2) p ((r,some j),some i) =
      regularityDirection (Yau.realVec i,0) (regularityDirection (Yau.realVec j,0)
        (fun z => jetValue (fun i => (Yau.realVec i,0)) U s z r)) p := rfl
  have hFirst (c : JetIndex α (Yau.RIdx n) s) (i : Yau.RIdx n) :
      jetValue (fun i => (Yau.realVec i,0)) U (s+2) p ((c,some i),none) =
      regularityDirection (Yau.realVec i,0) (fun z => jetValue (fun i => (Yau.realVec i,0)) U s z c) p := rfl
  have hValue (c : JetIndex α (Yau.RIdx n) s) :
      jetValue (fun i => (Yau.realVec i,0)) U (s+2) p ((c,none),none) =
      jetValue (fun i => (Yau.realVec i,0)) U s p c := rfl
  simp only [hSecond, hFirst, hValue, systemOperator, div_mul_eq_mul_div, ← Finset.sum_div]
  ring

end Yau.NodeProofs.P06Aux.CylinderReg
