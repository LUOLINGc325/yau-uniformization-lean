import Yau.Proofs.P06CylinderRegularityOneStep
import Yau.Proofs.P06CylinderRegularityHierarchy

/-! Arbitrary finite spatial L² jet energy on fixed interior buffers,
obtained by actual Caccioppoli and classical prolongation at every step. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates

variable {n : ℕ}

def jetIndexShiftEquiv (α ι : Type) : (s : ℕ) →
    JetIndex (RegularityProlongIndex α ι) ι s ≃ JetIndex α ι (s+1)
  | 0 => Equiv.refl _
  | s+1 => Equiv.prodCongr (jetIndexShiftEquiv α ι s) (Equiv.refl _)

theorem jetValue_prolong_shift {α : Type} [Fintype α] [DecidableEq α]
    (U : Point n → α → ℝ) (s : ℕ) (p : Point n)
    (r : JetIndex (RegularityProlongIndex α (Yau.RIdx n)) (Yau.RIdx n) s) :
    jetValue (fun i => (Yau.realVec i,0))
      (regularityProlongValue (fun i => (Yau.realVec i,0)) U) s p r =
      jetValue (fun i => (Yau.realVec i,0)) U (s+1) p
        (jetIndexShiftEquiv α (Yau.RIdx n) s r) := by
  induction s generalizing p with
  | zero => rfl
  | succ s ih =>
    rcases r with ⟨r,op⟩
    cases op with
    | none => exact ih p r
    | some i =>
      change regularityDirection (Yau.realVec i,0)
        (fun q => jetValue (fun j => (Yau.realVec j,0))
          (regularityProlongValue (fun j => (Yau.realVec j,0)) U) s q r) p =
        regularityDirection (Yau.realVec i,0)
          (fun q => jetValue (fun j => (Yau.realVec j,0)) U (s+1) q
            (jetIndexShiftEquiv α (Yau.RIdx n) s r)) p
      rw [show (fun q => jetValue (fun j => (Yau.realVec j,0))
          (regularityProlongValue (fun j => (Yau.realVec j,0)) U) s q r) =
        (fun q => jetValue (fun j => (Yau.realVec j,0)) U (s+1) q
          (jetIndexShiftEquiv α (Yau.RIdx n) s r)) from funext (fun q => ih q r)]

theorem jetValue_prolong_energy_shift {α : Type} [Fintype α] [DecidableEq α]
    (U : Point n → α → ℝ) (s : ℕ) (p : Point n) :
    valueSquare (jetValue (fun i => (Yau.realVec i,0))
      (regularityProlongValue (fun i => (Yau.realVec i,0)) U) s) p =
      valueSquare (jetValue (fun i => (Yau.realVec i,0)) U (s+1)) p := by
  classical
  unfold valueSquare
  simp_rw [jetValue_prolong_shift]
  exact Equiv.sum_comp (jetIndexShiftEquiv α (Yau.RIdx n) s)
    (fun r => (jetValue (fun i => (Yau.realVec i,0)) U (s+1) p r)^2)

theorem exists_spatial_energy_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j)) (N : ℕ) :
    ∀ (α : Type) [Fintype α] [DecidableEq α]
      (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ),
    (∀ r c i, ContDiff ℝ ∞ (e1 r c i)) → (∀ r c i, HasCompactSupport (e1 r c i)) →
    (∀ r c, ContDiff ℝ ∞ (e0 r c)) → (∀ r c, HasCompactSupport (e0 r c)) →
    ∀ {Q K : Set (Point n)}, IsOpen Q → IsCompact K → K ⊆ Q →
    ∀ (lam upper A : ℝ), 0 < lam → 0 ≤ A →
    Elliptic Q (heatPrincipal q) lam upper →
    (∀ p ∈ Q, ∀ i j, |heatPrincipal q p i j| ≤ A) →
    ∃ C : ℝ, 0 < C ∧ ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 Q U → IntegrableOn (valueSquare U) Q →
      (∫ p in K, valueSquare (jetValue (fun i => (Yau.realVec i,0)) U N) p) ≤
        C * ∫ p in Q, valueSquare U p := by
  induction N with
  | zero =>
    intro α _ _ e1 e0 he1 hce1 he0 hce0 Q K hQ hK hKQ lam upper A hlam hA hEll ha
    refine ⟨1,by norm_num,?_⟩
    intro U hU hPDE hUI
    change (∫ p in K, valueSquare U p) ≤ 1 * ∫ p in Q, valueSquare U p
    rw [one_mul]
    exact integral_valueSquare_mono hKQ hUI
  | succ N ih =>
    intro α _ _ e1 e0 he1 hce1 he0 hce0 Q K hQ hK hKQ lam upper A hlam hA hEll ha
    obtain ⟨V,hV,hKV,hVQ,hVC⟩ := exists_open_between_and_isCompact_closure hK hQ hKQ
    have hVsub : V ⊆ Q := subset_closure.trans hVQ
    let v : Yau.RIdx n → Point n := fun i => (Yau.realVec i,0)
    let e1' := regularityProlongE1 v q e1
    let e0' := regularityProlongE0 v e1 e0
    have hC1 := regularityProlongE1_regular v q e1 hq hcq he1 hce1
    have hC0 := regularityProlongE0_regular v e1 e0 he1 hce1 he0 hce0
    have hEllV : Elliptic V (heatPrincipal q) lam upper :=
      ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p (hVsub hp)⟩
    obtain ⟨C1,hC1pos,hStep⟩ := exists_one_step_energy_constant q e1 e0 hq hcq
      he1 hce1 he0 hce0 hQ hVC hVQ lam upper A hlam hA hEll ha
    obtain ⟨C2,hC2pos,hIter⟩ := ih (RegularityProlongIndex α (Yau.RIdx n)) e1' e0'
      (fun r c i => (hC1 r c i).1) (fun r c i => (hC1 r c i).2)
      (fun r c => (hC0 r c).1) (fun r c => (hC0 r c).2) hV hK hKV lam upper A
      hlam hA hEllV (fun p hp => ha p (hVsub hp))
    refine ⟨C2*C1,mul_pos hC2pos hC1pos,?_⟩
    intro U hU hPDE hUI
    let W := regularityProlongValue v U
    have hW (r) : ContDiff ℝ ∞ (fun p => W p r) := prolongValue_contDiff hU r
    have hWval : Continuous (valueSquare W) := (ContDiff.sum fun r _ => (hW r).pow 2).continuous
    have hWIclosure : IntegrableOn (valueSquare W) (closure V) :=
      hWval.continuousOn.integrableOn_compact hVC
    have hWI : IntegrableOn (valueSquare W) V := hWIclosure.mono_set subset_closure
    have hWPDE : heatEquation q e1' e0' V W := by
      have h := heatEquation_prolong q e1 e0 hQ U hq he1 he0 hU hPDE
      exact fun p hp r => h p (hVsub hp) r
    have hSecond := hIter W hW hWPDE hWI
    have hFirst := hStep U hU hPDE hUI
    have hMiddle := integral_valueSquare_mono (U := W) subset_closure hWIclosure
    have hCombined := hSecond.trans (mul_le_mul_of_nonneg_left (hMiddle.trans hFirst) hC2pos.le)
    dsimp only [W, v] at hCombined
    simp_rw [jetValue_prolong_energy_shift] at hCombined
    simpa only [mul_assoc] using hCombined

end Yau.NodeProofs.P06Aux.CylinderReg
