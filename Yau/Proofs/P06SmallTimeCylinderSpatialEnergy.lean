import Yau.Proofs.P06SmallTimeCylinderOneStep
import Yau.Proofs.P06CylinderRegularitySpatialIteration

/-! Finite spatial jet energy has exactly two inverse powers of the small
time per prolongation layer, with every constant selected before τ and U. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.ParabolicCandidates CylinderReg
variable {n : ℕ}

theorem exists_small_time_spatial_energy_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j)) (N : ℕ) :
    ∀ (α : Type) [Fintype α] [DecidableEq α]
      (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ),
    (∀ r c i, ContDiff ℝ ∞ (e1 r c i)) → (∀ r c i, HasCompactSupport (e1 r c i)) →
    (∀ r c, ContDiff ℝ ∞ (e0 r c)) → (∀ r c, HasCompactSupport (e0 r c)) →
    ∀ {Q K : Set (Point n)}, IsOpen Q → IsCompact K → K ⊆ Q →
    ∀ (lam upper A : ℝ), 0 < lam → 0 ≤ A →
    (∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      Elliptic (timeScale τ hτ.ne' '' Q) (heatPrincipal q) lam upper) →
    (∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ p ∈ timeScale τ hτ.ne' '' Q, ∀ i j, |heatPrincipal q p i j| ≤ A) →
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 (timeScale τ hτ.ne' '' Q) U →
      IntegrableOn (valueSquare U) (timeScale τ hτ.ne' '' Q) →
      (∫ p in timeScale τ hτ.ne' '' K,
        valueSquare (jetValue (fun i => (Yau.realVec i,0)) U N) p) ≤
        (C / τ ^ (2 * N)) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p := by
  induction N with
  | zero =>
    intro α _ _ e1 e0 he1 hce1 he0 hce0 Q K hQ hK hKQ lam upper A hlam hA hEll ha
    refine ⟨1, by norm_num, ?_⟩
    intro τ hτ hτ1 U hU hPDE hUI
    change (∫ p in timeScale τ hτ.ne' '' K, valueSquare U p) ≤
      (1 / τ ^ 0) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p
    rw [pow_zero, div_one, one_mul]
    exact integral_valueSquare_mono (Set.image_mono (f := timeScale τ hτ.ne') hKQ) hUI
  | succ N ih =>
    intro α _ _ e1 e0 he1 hce1 he0 hce0 Q K hQ hK hKQ lam upper A hlam hA hEll ha
    obtain ⟨V, hV, hKV, hVQ, hVC⟩ := exists_open_between_and_isCompact_closure hK hQ hKQ
    have hVsub : V ⊆ Q := subset_closure.trans hVQ
    let v : Yau.RIdx n → Point n := fun i => (Yau.realVec i,0)
    let e1' := regularityProlongE1 v q e1
    let e0' := regularityProlongE0 v e1 e0
    have hC1 := regularityProlongE1_regular v q e1 hq hcq he1 hce1
    have hC0 := regularityProlongE0_regular v e1 e0 he1 hce1 he0 hce0
    have hEllV : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
        Elliptic (timeScale τ hτ.ne' '' V) (heatPrincipal q) lam upper := by
      intro τ hτ hτ1
      have h := hEll τ hτ hτ1
      exact ⟨h.1, h.2.1, fun p hp => h.2.2 p (Set.image_mono hVsub hp)⟩
    obtain ⟨C1, hC1pos, hStep⟩ := exists_small_time_one_step_energy_constant q e1 e0 hq hcq
      he1 hce1 he0 hce0 hQ hVC hVQ lam upper A hlam hA hEll ha
    obtain ⟨C2, hC2pos, hIter⟩ := ih (RegularityProlongIndex α (Yau.RIdx n)) e1' e0'
      (fun r c i => (hC1 r c i).1) (fun r c i => (hC1 r c i).2)
      (fun r c => (hC0 r c).1) (fun r c => (hC0 r c).2) hV hK hKV lam upper A
      hlam hA hEllV (fun τ hτ hτ1 p hp => ha τ hτ hτ1 p (Set.image_mono hVsub hp))
    refine ⟨C2 * C1, mul_pos hC2pos hC1pos, ?_⟩
    intro τ hτ hτ1 U hU hPDE hUI
    let T := timeScale (n := n) τ hτ.ne'
    let W := regularityProlongValue v U
    have hW (r) : ContDiff ℝ ∞ (fun p => W p r) := prolongValue_contDiff hU r
    have hWval : Continuous (valueSquare W) := (ContDiff.sum fun r _ => (hW r).pow 2).continuous
    have hWIclosure : IntegrableOn (valueSquare W) (T '' closure V) :=
      hWval.continuousOn.integrableOn_compact (hVC.image T.continuous)
    have hWI : IntegrableOn (valueSquare W) (T '' V) :=
      hWIclosure.mono_set (Set.image_mono subset_closure)
    have hWPDE : heatEquation q e1' e0' (T '' V) W := by
      have h := heatEquation_prolong q e1 e0 (T.toHomeomorph.isOpenMap _ hQ)
        U hq he1 he0 hU hPDE
      exact fun p hp r => h p (Set.image_mono hVsub hp) r
    have hSecond := hIter τ hτ hτ1 W hW hWPDE hWI
    have hFirst := hStep τ hτ hτ1 U hU hPDE hUI
    have hMiddle := integral_valueSquare_mono (U := W) (Set.image_mono subset_closure) hWIclosure
    have hCombined := hSecond.trans (mul_le_mul_of_nonneg_left (hMiddle.trans hFirst)
      (div_nonneg hC2pos.le (pow_nonneg hτ.le _)))
    dsimp only [W, v] at hCombined
    simp_rw [jetValue_prolong_energy_shift] at hCombined
    convert hCombined using 1
    have hp : τ ^ (2 * (N + 1)) = τ ^ (2 * N) * τ ^ 2 := by
      rw [show 2 * (N + 1) = 2 * N + 2 by omega, pow_add]
    rw [hp]
    field_simp [hτ.ne']
    <;> ring

end Yau.NodeProofs.P06Aux.SmallTimeCylinder
