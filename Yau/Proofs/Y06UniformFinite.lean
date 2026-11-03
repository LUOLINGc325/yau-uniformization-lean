import Yau.Proofs.Y06ModelLayerBounds

/-! The exponents are fixed before one common late threshold is selected.
The resulting bound applies to every finite active mask and every horizon. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open Filter
open scoped Topology

variable {n d : ℕ}

theorem polySize_id_exp {A x : ℝ} (hA : (n + 1 : ℝ) ≤ A) (hx : 1 ≤ x) :
    polySize (PolyMap.id : PolyMap n) ≤ Real.exp (A * x) := by
  have hA0 : 0 ≤ A := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hAexp : A ≤ Real.exp A := by have := Real.add_one_le_exp A; linarith
  have hAx : A ≤ A * x := le_mul_of_one_le_right hA0 hx
  dsimp only [polySize]
  rw [coeffNorm_id]
  exact (by linarith : 1 + (n : ℝ) ≤ A).trans (hAexp.trans (Real.exp_le_exp.mpr hAx))

theorem uniform_finite_stage_bound (hd : 1 ≤ d)
    (aDiag : ℕ → Fin n → ℂ) (haDiag : ∀ k i, aDiag k i ≠ 0)
    (J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (P : ℕ → PolyMap n)
    (reg : ℕ → Prop) (x a : ℕ → ℝ) (k₀ : ℕ) {A L : ℝ}
    (hA : (n + 1 : ℝ) ≤ A) (hL : 0 ≤ L) (hx : ∀ k, 1 ≤ x k)
    (ha : ∀ k, 0 ≤ a k) (halim : Tendsto a atTop (𝓝 0))
    (hstep : ∀ k, reg k → x (k + 1) ≤ x k + L)
    (hP0 : ∀ k, (P k).FixesZero)
    (hPD : ∀ k, (P k).linearPart = Matrix.diagonal (aDiag k))
    (hJunit : ∀ k, reg k → IsUnit (J k))
    (hbudget : ∀ k, k₀ ≤ k → reg k →
      polySize (P k) ≤ Real.exp (A * x k) ∧
      polySize (linearPolynomial (J k)) ≤ Real.exp (A * x k) ∧
      polySize (linearPolynomial (J k)⁻¹) ≤ Real.exp (A * x k) ∧
      polySize (linearPolynomial (Matrix.diagonal (aDiag k))) ≤ Real.exp (A * x k) ∧
      polySize (linearPolynomial (Matrix.diagonal (aDiag k))⁻¹) ≤ Real.exp (A * x k))
    (hT : ∀ m, 2 ≤ m → m ≤ d → ∀ k, k₀ ≤ k → reg k →
      ∀ X : PolyMap n, Homogeneous X m →
        (backwardOperator (Matrix.diagonal (aDiag k)) (J k) (w k) X).coeffNorm ≤ a k * X.coeffNorm) :
    ∃ K : ℕ, k₀ ≤ K ∧ ∃ E : ℝ, 0 ≤ E ∧
      ∀ (b : ℕ) (active : ℕ → Prop),
        (∀ k, active k → K ≤ k ∧ reg k ∧ k < b) →
        let Q := finiteJetStage b active (fun k => Matrix.diagonal (aDiag k)) J w P (d - 1)
        ∀ k, polySize (Q.1 k) ≤ Real.exp (E * x k) ∧ polySize (Q.2 k) ≤ Real.exp (E * x k) := by
  classical
  have hA0 : 0 ≤ A := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  obtain ⟨Ksmall, hsmall⟩ := finite_stage_threshold halim d A L
  let K := max k₀ Ksmall
  let D := fun k => Matrix.diagonal (aDiag k)
  have hbound : ∀ r, r + 1 ≤ d → ∀ (b : ℕ) (active : ℕ → Prop),
      (∀ k, active k → K ≤ k ∧ reg k ∧ k < b) →
      let Q := finiteJetStage b active D J w P r
      ∀ k, polySize (Q.1 k) ≤ Real.exp (stageExponent d A L r * x k) ∧
        polySize (Q.2 k) ≤ Real.exp (stageExponent d A L r * x k) := by
    intro r
    induction r with
    | zero =>
      intro hr b active hactive
      change ∀ k : ℕ, polySize (PolyMap.id : PolyMap n) ≤ Real.exp (A * x k) ∧
        polySize (if active k then linearPolynomial (D k) else PolyMap.id) ≤ Real.exp (A * x k)
      intro k
      refine ⟨polySize_id_exp hA (hx k), ?_⟩
      by_cases hk : active k
      · rw [if_pos hk]
        exact (hbudget k ((le_max_left _ _).trans (hactive k hk).1) (hactive k hk).2.1).2.2.2.1
      · rw [if_neg hk]
        exact polySize_id_exp hA (hx k)
    | succ r ih =>
      intro hr b active hactive
      let old := finiteJetStage b active D J w P r
      let B := stageDiscrepancy (r + 2) P old.1 old.2 J
      let u := finiteLayerCorrection b active D J w B
      let v := finiteLayerModel b active D J w B
      let E := stageExponent d A L r
      let Bexp := ((d : ℝ) + 2 + L) * E + (2 * (d : ℝ) + 1) * A
      let Fexp := Bexp + A
      let Gexp := (Fexp + 2) * (1 + L) + (2 * (d : ℝ) + 1) * A + Bexp
      have hE : 0 ≤ E := stageExponent_nonneg d hA0 hL r
      have hF : 0 ≤ Fexp := stageForcingExponent_nonneg d hA0 hL r
      have hold : ∀ k, polySize (old.1 k) ≤ Real.exp (E * x k) ∧
          polySize (old.2 k) ≤ Real.exp (E * x k) := ih (by omega) b active hactive
      have hSpec : FiniteStageSpec active D J w P old.1 old.2 (r + 1) :=
        finiteJetStage_spec b active aDiag haDiag J (fun k hk => hJunit k (hactive k hk).2.1)
          w P hP0 hPD (fun k hk => (hactive k hk).2.2) r
      have hB : ∀ k, Homogeneous (B k) (r + 2) := stageDiscrepancy_homogeneous _ _ _ _ _
      have hu : ∀ k, Homogeneous (u k) (r + 2) := finiteLayerCorrection_homogeneous b active D J w B hB
      have hBbound : ∀ k, active k → polySize (B k) ≤ Real.exp (Bexp * x k) := by
        intro k hk
        obtain ⟨hPb, hJb, hJib, hDb, hDib⟩ :=
          hbudget k ((le_max_left _ _).trans (hactive k hk).1) (hactive k hk).2.1
        exact stageDiscrepancy_size P old.1 old.2 J k (r + 2)
          ((hSpec.2.1 (k + 1)).2.1.trans (by omega))
          ((hSpec.2.2 k hk).2.2.1.trans (by omega)) hPb hJb hJib
          (hold k).1 (exp_next_size hE (hx k) hL (hstep k (hactive k hk).2.1) (hold (k + 1)).1) (hold k).2
      have hforce : ∀ k, active k →
          (forbiddenProjection (w k) ((linearPolynomial (D k)⁻¹).comp (B k))).coeffNorm ≤ Real.exp (Fexp * x k) := by
        intro k hk
        have hDib := (hbudget k ((le_max_left _ _).trans (hactive k hk).1) (hactive k hk).2.1).2.2.2.2
        have hf := projected_forcing_size (D k) (w k) (B k) hDib (hBbound k hk)
        have hnorm : (forbiddenProjection (w k) ((linearPolynomial (D k)⁻¹).comp (B k))).coeffNorm ≤
            polySize (forbiddenProjection (w k) ((linearPolynomial (D k)⁻¹).comp (B k))) := by dsimp [polySize]; linarith
        exact hnorm.trans (by simpa only [Fexp, add_comm] using hf)
      have huBound : ∀ k, (u k).coeffNorm ≤ Real.exp ((Fexp + 1) * x k) := by
        refine finiteLayerCorrection_coeff_envelope b active D J w B hB x a
          (F := Fexp) (L := L) hx ha (by linarith) ?_ ?_ hforce ?_
        · intro k hk
          exact hstep k (hactive k hk).2.1
        · intro k hk X hX
          exact hT (r + 2) (by omega) (by omega) k
            ((le_max_left _ _).trans (hactive k hk).1) (hactive k hk).2.1 X hX
        · intro k hk
          exact hsmall k ((le_max_right _ _).trans (hactive k hk).1) r (by omega)
      have huSize : ∀ k, polySize (u k) ≤ Real.exp ((Fexp + 2) * x k) := by
        intro k
        apply (add_le_add (le_refl 1) (huBound k)).trans
        simpa only [max_eq_right (by linarith : 0 ≤ Fexp + 1), add_assoc, one_add_one_eq_two] using
          one_add_exp_enlarge (A := Fexp + 1) (hx k)
      change ∀ k : ℕ, polySize (old.1 k + u k) ≤ Real.exp (stageExponent d A L (r + 1) * x k) ∧
        polySize (old.2 k + v k) ≤ Real.exp (stageExponent d A L (r + 1) * x k)
      intro k
      have hNew : stageExponent d A L (r + 1) = E + max (Fexp + 2) Gexp := by
        dsimp only [stageExponent, E, Fexp, Bexp, Gexp]
        congr 2 <;> ring
      rw [hNew]
      refine ⟨(polySize_exp_add (hold k).1 (huSize k)).trans (Real.exp_le_exp.mpr ?_), ?_⟩
      · exact mul_le_mul_of_nonneg_right (add_le_add (le_refl E) (le_max_left _ _)) (by linarith [hx k])
      · by_cases hk : active k
        · obtain ⟨hPb, hJb, hJib, hDb, hDib⟩ :=
            hbudget k ((le_max_left _ _).trans (hactive k hk).1) (hactive k hk).2.1
          have huNext := exp_next_size (by linarith : 0 ≤ Fexp + 2) (hx k) hL
            (hstep k (hactive k hk).2.1) (huSize (k + 1))
          have hvSize : polySize (v k) ≤ Real.exp (Gexp * x k) := by
            have hvBound := finiteLayerModel_size (d := d) b active D J w B k (H := Fexp + 1) hk
              ((homogeneous_degree_le (hu (k + 1))).trans (by omega))
              (by simpa only [add_assoc, one_add_one_eq_two] using huNext) hJb hJib hDb (hBbound k hk)
            simpa only [v, Gexp, add_assoc, one_add_one_eq_two] using hvBound
          exact (polySize_exp_add (hold k).2 hvSize).trans
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (add_le_add (le_refl E) (le_max_right _ _)) (by linarith [hx k])))
        · have hv0 : v k = 0 := by
            classical
            change (if active k then _ else 0) = 0
            exact ite_eq_right hk
          rw [hv0, add_zero]
          exact (hold k).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right ((by linarith : 0 ≤ Fexp + 2).trans (le_max_left _ _))) (by linarith [hx k])))
  refine ⟨K, le_max_left _ _, stageExponent d A L (d - 1), stageExponent_nonneg d hA0 hL _, ?_⟩
  exact hbound (d - 1) (by omega)

end Yau.Proofs.Y06Aux
