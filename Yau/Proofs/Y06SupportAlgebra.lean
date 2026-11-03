import Yau.Proofs.Y06FiniteLayer
import Yau.Proofs.Y06StrictWeight

/-! Nonlinear support and tangent data survive the actual homogeneous updates. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

def OnlyForbidden (P : PolyMap n) (w : Fin n → ℝ) : Prop :=
  ∀ i (β : Fin n →₀ ℕ), 2 ≤ β.sum (fun _ e => e) →
    (P i).coeff β ≠ 0 → w i < ∑ l, (β l : ℝ) * w l

theorem onlyForbidden_linearPolynomial (A : Herm n) (w : Fin n → ℝ) :
    OnlyForbidden (linearPolynomial A) w := by
  intro i β hβ hn
  exact False.elim (hn (linearPolynomial_coeff_higher A i β hβ))

theorem onlyForbidden_id (w : Fin n → ℝ) : OnlyForbidden (PolyMap.id : PolyMap n) w := by
  have hid : linearPolynomial (1 : Herm n) = PolyMap.id := linearPoly_one
  rw [← hid]
  exact onlyForbidden_linearPolynomial 1 w

theorem onlyForbidden_add {P Q : PolyMap n} {w : Fin n → ℝ}
    (hP : OnlyForbidden P w) (hQ : OnlyForbidden Q w) : OnlyForbidden (P + Q) w := by
  intro i β hβ hn
  by_cases hp : (P i).coeff β = 0
  · apply hQ i β hβ
    intro hq
    apply hn
    change (P i).coeff β + (Q i).coeff β = 0
    rw [hp, hq, add_zero]
  · exact hP i β hβ hp

theorem allowed_add {P Q : PolyMap n} {w : Fin n → ℝ}
    (hP : Allowed P w) (hQ : Allowed Q w) : Allowed (P + Q) w := by
  intro i β hβ hn
  by_cases hp : (P i).coeff β = 0
  · apply hQ i β hβ
    intro hq
    apply hn
    change (P i).coeff β + (Q i).coeff β = 0
    rw [hp, hq, add_zero]
  · exact hP i β hβ hp

theorem allowed_linearPolynomial (A : Herm n) (w : Fin n → ℝ) :
    Allowed (linearPolynomial A) w := by
  intro i β hβ hn
  exact False.elim (hn (linearPolynomial_coeff_higher A i β hβ))

theorem onlyForbidden_of_projection {P : PolyMap n} {w : Fin n → ℝ}
    (hP : forbiddenProjection w P = P) : OnlyForbidden P w := by
  intro i β hβ hn
  have hcoeff := congrArg (fun Q : PolyMap n => (Q i).coeff β) hP
  rw [forbiddenProjection_coeff] at hcoeff
  by_contra hnot
  rw [ite_eq_right hnot] at hcoeff
  exact hn hcoeff.symm

theorem finiteLayerCorrection_forbidden (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n) (k : ℕ) :
    OnlyForbidden (finiteLayerCorrection b active D J w B k) (w k) := by
  by_cases hk : k < b
  · by_cases hact : active k
    · rw [finiteLayerCorrection_step b active D J w B hk hact]
      exact onlyForbidden_of_projection (backwardAffineStep_forbidden _ _ _ _ _)
    · rw [finiteLayerCorrection_inactive b active D J w B hact]
      intro i β hβ hn
      exact False.elim (hn rfl)
  · rw [finiteLayerCorrection_terminal b active D J w B (by omega)]
    intro i β hβ hn
    exact False.elim (hn rfl)

theorem finiteLayerModel_allowed (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n) (k : ℕ) :
    Allowed (finiteLayerModel b active D J w B k) (w k) := by
  classical
  unfold finiteLayerModel
  split_ifs
  · exact allowedProjection_allowed _ _
  · intro i β hβ hn; exact False.elim (hn rfl)

theorem tangentId_add_homogeneous {H u : PolyMap n} (hH : tangentId H)
    (hu : Homogeneous u m) (hm : 2 ≤ m) : tangentId (H + u) := by
  rw [tangentId_iff_jetEq] at hH ⊢
  have hz : PolyMap.JetEq u 0 1 := by
    apply (jetEq_iff_order u 0 1).mpr
    simpa only [sub_zero] using mapOrderAtLeast_mono (homogeneous_order hu) hm
  have h := jetEq_add hH hz
  simpa only [add_zero] using h

end Yau.Proofs.Y06Aux
