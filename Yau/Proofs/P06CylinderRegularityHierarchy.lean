import Yau.Proofs.P06CylinderRegularityProlongationHeat

/-! The explicit finite spatial jet hierarchy and its actual equations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic

def JetIndex (α ι : Type) : ℕ → Type
  | 0 => α
  | s+1 => RegularityProlongIndex (JetIndex α ι s) ι

instance jetIndexFintype (α ι : Type) [Fintype α] [Fintype ι] (s : ℕ) :
    Fintype (JetIndex α ι s) := by
  induction s with
  | zero => exact inferInstanceAs (Fintype α)
  | succ s ih =>
    letI : Fintype (JetIndex α ι s) := ih
    change Fintype (JetIndex α ι s × Option ι)
    infer_instance

instance jetIndexDecidableEq (α ι : Type) [DecidableEq α] [DecidableEq ι] (s : ℕ) :
    DecidableEq (JetIndex α ι s) := by
  induction s with
  | zero => exact inferInstanceAs (DecidableEq α)
  | succ s ih =>
    letI : DecidableEq (JetIndex α ι s) := ih
    change DecidableEq (JetIndex α ι s × Option ι)
    infer_instance

variable {E : Type*} {ι α : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

def jetValue (v : ι → E) (U : E → α → ℝ) : (s : ℕ) → E → JetIndex α ι s → ℝ
  | 0 => U
  | s+1 => regularityProlongValue v (jetValue v U s)

def jetE1 (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) :
    (s : ℕ) → JetIndex α ι s → JetIndex α ι s → ι → E → ℝ
  | 0 => e1
  | s+1 => regularityProlongE1 v q (jetE1 v q e1 s)

def jetE0 (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) :
    (s : ℕ) → JetIndex α ι s → JetIndex α ι s → E → ℝ
  | 0 => e0
  | s+1 => regularityProlongE0 v (jetE1 v q e1 s) (jetE0 v q e1 e0 s)

theorem jetValue_contDiff (v : ι → E) {U : E → α → ℝ}
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (s : ℕ) (r : JetIndex α ι s) :
    ContDiff ℝ ∞ (fun p => jetValue v U s p r) := by
  induction s with
  | zero => exact hU r
  | succ s ih =>
    rcases r with ⟨r,op⟩
    cases op with
    | none => exact ih r
    | some i => exact regularityDirection_contDiff (ih r) (v i)

theorem jetValue_compact (v : ι → E) {U : E → α → ℝ}
    (hU : ∀ r, HasCompactSupport (fun p => U p r)) (s : ℕ) (r : JetIndex α ι s) :
    HasCompactSupport (fun p => jetValue v U s p r) := by
  induction s with
  | zero => exact hU r
  | succ s ih =>
    rcases r with ⟨r,op⟩
    cases op with
    | none => exact ih r
    | some i => exact (ih r).fderiv_apply ℝ (v i)

theorem jetCoefficients_regular (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c)) (s : ℕ) :
    (∀ r c i, ContDiff ℝ ∞ (jetE1 v q e1 s r c i) ∧ HasCompactSupport (jetE1 v q e1 s r c i)) ∧
    ∀ r c, ContDiff ℝ ∞ (jetE0 v q e1 e0 s r c) ∧ HasCompactSupport (jetE0 v q e1 e0 s r c) := by
  induction s with
  | zero => exact ⟨fun r c i => ⟨he1 r c i,hce1 r c i⟩, fun r c => ⟨he0 r c,hce0 r c⟩⟩
  | succ s ih =>
    refine ⟨?_,?_⟩
    · intro r c i
      exact regularityProlongE1_regular v q (jetE1 v q e1 s) hq hcq
        (fun r c i => (ih.1 r c i).1) (fun r c i => (ih.1 r c i).2) r c i
    · intro r c
      exact regularityProlongE0_regular v (jetE1 v q e1 s) (jetE0 v q e1 e0 s)
        (fun r c i => (ih.1 r c i).1) (fun r c i => (ih.1 r c i).2)
        (fun r c => (ih.2 r c).1) (fun r c => (ih.2 r c).2) r c

theorem jetValue_heatEquation {n : ℕ}
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    {Q : Set (Point n)} (hQ : IsOpen Q) (U : Point n → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (hPDE : heatEquation q e1 e0 Q U) (s : ℕ) :
    heatEquation q (jetE1 (fun i => (Yau.realVec i,0)) q e1 s)
      (jetE0 (fun i => (Yau.realVec i,0)) q e1 e0 s) Q
      (jetValue (fun i => (Yau.realVec i,0)) U s) := by
  induction s with
  | zero => exact hPDE
  | succ s ih =>
    have hC := jetCoefficients_regular (fun i => (Yau.realVec i,0)) q e1 e0 hq hcq he1 hce1 he0 hce0 s
    exact heatEquation_prolong q _ _ hQ _ hq
      (fun r c i => (hC.1 r c i).1) (fun r c => (hC.2 r c).1)
      (jetValue_contDiff _ hU s) ih

end Yau.NodeProofs.P06Aux.CylinderReg
