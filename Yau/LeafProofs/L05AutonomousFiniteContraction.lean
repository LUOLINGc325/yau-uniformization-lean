import Yau.LeafProofs.L05AutonomousFiniteContractionExtrema

open MeasureTheory Set
open scoped BigOperators

namespace Yau.LeafProofs.L05AutonomousAux

/-- The uniform coefficient selected before the space and the scalar fields. -/
noncomputable def finiteContractionA (m : ℕ) (a b p CH : ℝ) : ℝ :=
  (b / a) * CH * (m : ℝ) ^ (1 / p)

/-- The actual contraction factor selected solely from scalar data. -/
noncomputable def finiteContractionTheta (m : ℕ) (a b p CH : ℝ) : ℝ :=
  finiteContractionA m a b p CH / (1 + finiteContractionA m a b p CH)

theorem finite_contraction_constants {m : ℕ} (hm : 0 < m) {a b p CH : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hCH : 0 < CH) :
    0 < finiteContractionA m a b p CH ∧
    0 < finiteContractionTheta m a b p CH ∧
    finiteContractionTheta m a b p CH < 1 := by
  have hb : 0 < b := ha.trans_le hab
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hA : 0 < finiteContractionA m a b p CH := by
    unfold finiteContractionA
    exact mul_pos (mul_pos (div_pos hb ha) hCH) (Real.rpow_pos_of_pos hm' _)
  refine ⟨hA, div_pos hA (by linarith), ?_⟩
  unfold finiteContractionTheta
  exact (div_lt_one (by linarith)).mpr (by linarith)

/-- The literal finite-family contraction, with genuine extrema and probability integrals. -/
theorem finite_oscillation_contraction (m : ℕ) (a b p CH : ℝ)
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) (hp1 : p < 1) (hCH : 0 < CH)
    {X : Type*} [MeasurableSpace X] (Qsmall Q E : Set X)
    (hsmall : Qsmall.Nonempty) (hsmallQ : Qsmall ⊆ Q) (hEQ : E ⊆ Q)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : ∀ᵐ q ∂μ, q ∈ E)
    (w : Fin m → X → ℝ) (hw : ∀ i, Measurable (w i))
    (hU : ∀ i, BddAbove (w i '' Q)) (hL : ∀ i, BddBelow (w i '' Q))
    (hsecant : ∀ x ∈ Qsmall, ∀ q ∈ E, ∃ c : Fin m → ℝ,
      (∀ i, c i ∈ Icc a b) ∧ ∑ i, c i * (w i x - w i q) = 0)
    (hmean : ∀ i,
      (∫ q, (max (finiteFieldSup (w i) Q - w i q) 0) ^ p ∂μ) ^ (1 / p) ≤
        CH * (finiteFieldSup (w i) Q - finiteFieldSup (w i) Qsmall)) :
    (∑ i, (finiteFieldSup (w i) Qsmall - finiteFieldInf (w i) Qsmall)) ≤
      finiteContractionTheta m a b p CH *
        ∑ i, (finiteFieldSup (w i) Q - finiteFieldInf (w i) Q) := by
  classical
  let M : Fin m → ℝ := fun i => finiteFieldSup (w i) Q
  let MS : Fin m → ℝ := fun i => finiteFieldSup (w i) Qsmall
  let mS : Fin m → ℝ := fun i => finiteFieldInf (w i) Qsmall
  let mo : Fin m → ℝ := fun i => finiteFieldInf (w i) Q
  let D : Fin m → X → ℝ := fun i q => max (M i - w i q) 0
  have hQ : Q.Nonempty := hsmall.mono hsmallQ
  have hext := fun i => finite_extrema_nested (w i) hsmall hsmallQ (hU i) (hL i)
  have hM : ∀ i, ∀ x ∈ Q, w i x ≤ M i :=
    fun i x hx => le_csSup (hU i) (mem_image_of_mem (w i) hx)
  have hMS : ∀ i, MS i ≤ M i := fun i => (hext i).2.2.2.2.1
  have hmS : ∀ i, mo i ≤ mS i := fun i => (hext i).2.2.2.2.2.1
  have hDI : ∀ i, Integrable (fun q => (D i q) ^ p) μ := fun i =>
    (finite_deficit_integrable μ (w i) (hw i) hEQ hμ hQ (hU i) (hL i) hp).2
  have hDmeas : ∀ i, Measurable (D i) := fun i =>
    (measurable_const.sub (hw i)).max measurable_const
  have hD0 : ∀ i, ∀ᵐ q ∂μ, 0 ≤ D i q := fun i =>
    Filter.Eventually.of_forall fun q => le_max_right _ _
  obtain ⟨hsumI, htriangle⟩ := finite_integral_rpow_sum μ hm hp hp1 D hDmeas hD0 hDI
  let G : ℝ := ∑ i, (M i - MS i)
  let C : ℝ := (b / a) * ((m : ℝ) ^ (1 / p - 1) * (CH * G))
  have hK : 0 ≤ b / a := (div_pos (ha.trans_le hab) ha).le
  have hmeanSum : (∑ i, (∫ q, (D i q) ^ p ∂μ) ^ (1 / p)) ≤ CH * G := by
    calc
      _ ≤ ∑ i, CH * (M i - MS i) := Finset.sum_le_sum fun i _ => hmean i
      _ = _ := by dsimp [G]; rw [Finset.mul_sum]
  have hpoint : ∀ j, ∀ x ∈ Qsmall, M j - w j x ≤ C := by
    intro j x hx
    have hbound : ∀ᵐ q ∂μ, M j - w j x ≤ (b / a) * ∑ i, D i q := by
      filter_upwards [hμ] with q hq
      obtain ⟨c, hc, heq⟩ := hsecant x hx q hq
      have hd := finite_deficit_comparison ha hab M (fun i => w i x) (fun i => w i q) c
        (fun i => hM i x (hsmallQ hx)) (fun i => hM i q (hEQ hq)) hc heq j
      simpa only [D, max_eq_left (sub_nonneg.mpr (hM _ q (hEQ hq)))] using hd
    calc
      _ ≤ (b / a) * (∫ q, (∑ i, D i q) ^ p ∂μ) ^ (1 / p) :=
        finite_constant_le_mean μ hp (sub_nonneg.mpr (hM j x (hsmallQ hx))) hK
          (fun q => ∑ i, D i q)
          (Filter.Eventually.of_forall fun q => Finset.sum_nonneg fun i _ => le_max_right _ _)
          hsumI hbound
      _ ≤ (b / a) * ((m : ℝ) ^ (1 / p - 1) *
          ∑ i, (∫ q, (D i q) ^ p ∂μ) ^ (1 / p)) := mul_le_mul_of_nonneg_left htriangle hK
      _ ≤ C := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmeanSum (Real.rpow_nonneg (Nat.cast_nonneg m) _)) hK
  have hosci : ∀ i, MS i - mS i ≤ C := by
    intro i
    have hinf : M i - C ≤ mS i := by
      apply le_csInf (hext i).2.1
      rintro v ⟨x, hx, rfl⟩
      linarith [hpoint i x hx]
    linarith [hMS i]
  have hosc : (∑ i, (MS i - mS i)) ≤ finiteContractionA m a b p CH * G := by
    calc
      _ ≤ ∑ _i : Fin m, C := Finset.sum_le_sum fun i _ => hosci i
      _ = (m : ℝ) * C := by simp
      _ = _ := by
        have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
        have hfactor : (m : ℝ) * (m : ℝ) ^ (1 / p - 1) = (m : ℝ) ^ (1 / p) := by
          calc
            _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (1 / p - 1) := by rw [Real.rpow_one]
            _ = (m : ℝ) ^ (1 + (1 / p - 1)) := (Real.rpow_add hm' _ _).symm
            _ = _ := by congr 1; ring
        dsimp [C, finiteContractionA]
        calc
          _ = (b / a) * CH * ((m : ℝ) * (m : ℝ) ^ (1 / p - 1)) * G := by ring
          _ = _ := by rw [hfactor]
  have hgap : G ≤ (∑ i, (M i - mo i)) - ∑ i, (MS i - mS i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => by dsimp [G] at *; linarith [hmS i]
  have hA := (finite_contraction_constants (p := p) hm ha hab hCH).1
  have hcombined : (1 + finiteContractionA m a b p CH) * (∑ i, (MS i - mS i)) ≤
      finiteContractionA m a b p CH * (∑ i, (M i - mo i)) := by
    nlinarith [mul_le_mul_of_nonneg_left hgap hA.le]
  change (∑ i, (MS i - mS i)) ≤ _
  unfold finiteContractionTheta
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (by linarith : 0 < 1 + finiteContractionA m a b p CH)).mpr
    (by nlinarith [hcombined])

/-- The contraction constant is chosen before every space, set, measure, and field. -/
theorem exists_finite_oscillation_contraction (m : ℕ) (a b p CH : ℝ)
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) (hp1 : p < 1) (hCH : 0 < CH) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ {X : Type*} [MeasurableSpace X] (Qsmall Q E : Set X),
        Qsmall.Nonempty → Qsmall ⊆ Q → E ⊆ Q →
        ∀ (μ : Measure X) [IsProbabilityMeasure μ], (∀ᵐ q ∂μ, q ∈ E) →
        ∀ (w : Fin m → X → ℝ), (∀ i, Measurable (w i)) →
          (∀ i, BddAbove (w i '' Q)) → (∀ i, BddBelow (w i '' Q)) →
          (∀ x ∈ Qsmall, ∀ q ∈ E, ∃ c : Fin m → ℝ,
            (∀ i, c i ∈ Icc a b) ∧ ∑ i, c i * (w i x - w i q) = 0) →
          (∀ i, (∫ q, (max (finiteFieldSup (w i) Q - w i q) 0) ^ p ∂μ) ^ (1 / p) ≤
            CH * (finiteFieldSup (w i) Q - finiteFieldSup (w i) Qsmall)) →
          (∑ i, (finiteFieldSup (w i) Qsmall - finiteFieldInf (w i) Qsmall)) ≤
            θ * ∑ i, (finiteFieldSup (w i) Q - finiteFieldInf (w i) Q) := by
  obtain ⟨_, hθ0, hθ1⟩ := finite_contraction_constants (p := p) hm ha hab hCH
  refine ⟨finiteContractionTheta m a b p CH, hθ0, hθ1, ?_⟩
  intro X inst Qsmall Q E hsmall hsmallQ hEQ μ instμ hμ w hw hU hL hsecant hmean
  exact finite_oscillation_contraction m a b p CH hm ha hab hp hp1 hCH
    Qsmall Q E hsmall hsmallQ hEQ μ hμ w hw hU hL hsecant hmean

end Yau.LeafProofs.L05AutonomousAux
