import Yau.Proofs.Y03MatrixTopology
import Yau.Proofs.Y03Conjugation

/-! Exact change identities, uniform bounds and jump zeros pass to one coefficientwise limit. -/

open scoped Topology Matrix Matrix.Norms.Elementwise
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem changeAt_limit (D : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (J : ℕ → ℕ) (S : ℕ → ℝ)
    (C c : ℝ) (k : ℕ) (hD : IsUnit (D k)) {L : ℕ → Changes n} {P M : Herm n}
    (hp : Tendsto (fun H => (L H).plus k) atTop (𝓝 P))
    (hm : Tendsto (fun H => (L H).minus k) atTop (𝓝 M))
    (hchange : ∀ᶠ H in atTop, ChangeAt D w J S C c (L H) k) :
    ChangeAt D w J S C c (⟨fun _ => P, fun _ => M⟩ : Changes n) k := by
  have htri := strict_weight_eventual_limit (w k) hp
    (hchange.mono fun H hH => hH.1) (hchange.mono fun H hH => hH.2.1)
  have hP : IsUnit P := strict_weight_isUnit P (w k) htri.1 htri.2
  have hpinv := matrix_inverse_tendsto_of_isUnit hp hP
  have hform : M = (D k)⁻¹ * P * D k := by
    have hlim : Tendsto (fun H => (D k)⁻¹ * (L H).plus k * D k) atTop (𝓝 ((D k)⁻¹ * P * D k)) :=
      (tendsto_const_nhds.mul hp).mul tendsto_const_nhds
    have heq : (fun H => (L H).minus k) =ᶠ[atTop] fun H => (D k)⁻¹ * (L H).plus k * D k :=
      hchange.mono fun H hH => hH.2.2.1
    exact tendsto_nhds_unique (hm.congr' heq) hlim
  have hnorm : matOpNorm P + matOpNorm P⁻¹ ≤ (1 + (J k : ℝ)) ^ C := by
    apply le_of_tendsto (((continuous_matOpNorm.tendsto P).comp hp).add
      ((continuous_matOpNorm.tendsto P⁻¹).comp hpinv))
    exact hchange.mono fun H hH => hH.2.2.2.2.1
  have hsmall : matOpNorm (M - 1) ≤
      (1 + (J k : ℝ)) ^ C * Real.exp (-c * Real.sqrt (S (J k)) / (J k : ℝ) ^ 2) := by
    apply le_of_tendsto ((continuous_matOpNorm.tendsto (M - 1)).comp (hm.sub tendsto_const_nhds))
    exact hchange.mono fun H hH => hH.2.2.2.2.2
  refine ⟨htri.1, htri.2, hform, ?_, hnorm, hsmall⟩
  rw [hform]
  exact diagonal_change_identity (D k) P hD hP

theorem jump_entries_limit (E : Frames n) (w : ℕ → Fin n → ℝ) (k : ℕ)
    {L : ℕ → Changes n} {P Mnext : Herm n} (hP : IsUnit P)
    (hp : Tendsto (fun H => (L H).plus k) atTop (𝓝 P))
    (hm : Tendsto (fun H => (L H).minus (k + 1)) atTop (𝓝 Mnext))
    (hjump : ∀ᶠ H in atTop, JumpAt E w (L H) k) :
    ∀ i l, w (k + 1) i < w k l → (Mnext * jump E k * P⁻¹) i l = 0 := by
  have hpinv := matrix_inverse_tendsto_of_isUnit hp hP
  have hprod : Tendsto (fun H => (L H).minus (k + 1) * jump E k * ((L H).plus k)⁻¹) atTop
      (𝓝 (Mnext * jump E k * P⁻¹)) := (hm.mul tendsto_const_nhds).mul hpinv
  intro i l hil
  have hcoord := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hprod i) l
  have heq : (fun H => ((L H).minus (k + 1) * jump E k * ((L H).plus k)⁻¹) i l) =ᶠ[atTop]
      fun _ => (0 : ℂ) := hjump.mono fun H hH => hH i l hil
  exact tendsto_nhds_unique hcoord (tendsto_const_nhds.congr' heq.symm)

end Yau.Blueprint.Alignment.Y03Proof
