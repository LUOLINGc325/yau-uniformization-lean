import Yau.LeafProofs.L17UniformCharts

/-! Exact ellipticity constants for the original scalar Chern principal symbol. -/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ}

theorem posDef_inverse_order
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) : (A⁻¹ - B⁻¹).PosSemidef := by
  classical
  have hpos : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A := hA.posSemidef.nonneg
  have hab : A ≤ B := hAB
  have h := CStarAlgebra.inv_le_inv (a := hA.isUnit.unit) (b := hB.isUnit.unit)
    (by simpa only [IsUnit.unit_spec] using hpos)
    (by simpa only [IsUnit.unit_spec] using hab)
  have h' : B⁻¹ ≤ A⁻¹ := by
    simpa only [Matrix.coe_units_inv, IsUnit.unit_spec] using h
  exact Matrix.le_iff.mp h'

theorem inverse_real_smul_one (c : ℝ) (hc : c ≠ 0) :
    (((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹) =
      ((c⁻¹ : ℝ) : ℂ) • 1 := by
  classical
  let : Invertible (c : ℂ) := invertibleOfNonzero (by exact_mod_cast hc)
  have h := Matrix.inv_smul (A := (1 : Matrix (Fin n) (Fin n) ℂ)) (c : ℂ) (by simp)
  simpa [invOf_eq_inv] using h

theorem inverse_matrix_comparison
    {G : Matrix (Fin n) (Fin n) ℂ} {C : ℝ} (hG : G.PosDef) (hC : 0 < C)
    (hlo : (G - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef)
    (hhi : ((C : ℂ) • 1 - G).PosSemidef) :
    (G⁻¹ - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      ((C : ℂ) • 1 - G⁻¹).PosSemidef := by
  have hp : ((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hC)
  have hpi : (((C⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr (inv_pos.mpr hC))
  have hl := posDef_inverse_order hG hp hhi
  have hh := posDef_inverse_order hpi hG hlo
  rw [inverse_real_smul_one C hC.ne'] at hl
  rw [inverse_real_smul_one C⁻¹ (inv_ne_zero hC.ne'), inv_inv] at hh
  exact ⟨hl, hh⟩

theorem scalarRealification_sub (A B : Matrix (Fin n) (Fin n) ℂ) :
    scalarRealification (A - B) = scalarRealification A - scalarRealification B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [scalarRealification]
  ring

theorem scalarRealification_real_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    scalarRealification ((c : ℂ) • A) = c • scalarRealification A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [scalarRealification, Complex.mul_re, Complex.mul_im]

theorem scalarRealification_one :
    scalarRealification (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    fin_cases a <;> fin_cases b <;> simp [scalarRealification]
  · fin_cases a <;> fin_cases b <;>
      simp [scalarRealification, hij, Prod.mk.injEq]

theorem scalarSymbol_comparison
    {G : Matrix (Fin n) (Fin n) ℂ} {C : ℝ} (hG : G.PosDef) (hC : 0 < C)
    (hlo : (G - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef)
    (hhi : ((C : ℂ) • 1 - G).PosSemidef) :
    (scalarSymbol G - ((1 / 4 : ℝ) * C⁻¹) • 1).PosSemidef ∧
      (((1 / 4 : ℝ) * C) • 1 - scalarSymbol G).PosSemidef := by
  obtain ⟨hl, hh⟩ := inverse_matrix_comparison hG hC hlo hhi
  have hlr := scalarRealification_posSemidef hl
  have hhr := scalarRealification_posSemidef hh
  simp only [scalarRealification_sub, scalarRealification_real_smul,
    scalarRealification_one] at hlr hhr
  constructor
  · simpa only [smul_sub, smul_smul, scalarSymbol] using
      hlr.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
  · simpa only [smul_sub, smul_smul, scalarSymbol] using
      hhr.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)

theorem scalarSymbol_ellipticity
    {G : Matrix (Fin n) (Fin n) ℂ} {C : ℝ} (hG : G.PosDef) (hC : 0 < C)
    (hlo : (G - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef)
    (hhi : ((C : ℂ) • 1 - G).PosSemidef) :
    (scalarSymbol G - ((4 * C)⁻¹ : ℝ) • 1).PosSemidef ∧
      ((C / 4 : ℝ) • 1 - scalarSymbol G).PosSemidef := by
  obtain ⟨hl, hh⟩ := scalarSymbol_comparison hG hC hlo hhi
  have heq : (1 / 4 : ℝ) * C⁻¹ = (4 * C)⁻¹ := by simp only [one_div, mul_inv_rev, mul_comm]
  have heq' : (1 / 4 : ℝ) * C = C / 4 := by ring
  rw [heq] at hl
  rw [heq'] at hh
  exact ⟨hl, hh⟩

theorem BoundedChartFamily.scalarSymbol_ellipticity
    {M : ComplexManifold n} {g : HermitianField M} (A : BoundedChartFamily g)
    (p : M.Carrier) {z : ComplexVector n} (hz : z ∈ Metric.ball 0 A.radius) :
    (scalarSymbol (pullbackMatrix g (A.chart p) z) - ((4 * A.bound 0)⁻¹ : ℝ) • 1).PosSemidef ∧
      ((A.bound 0 / 4 : ℝ) • 1 - scalarSymbol (pullbackMatrix g (A.chart p) z)).PosSemidef := by
  have hs : z ∈ (A.chart p).source := A.closedBall_source p (Metric.ball_subset_closedBall hz)
  apply Yau.LeafProofs.L17Aux.scalarSymbol_ellipticity
    (pullbackMatrix_posDef g (A.chart p) (A.differentiable p) (A.inverse_differentiable p) hs)
    (A.bound_pos 0) _ (A.comparison p z hz).2
  simpa only [Complex.ofReal_inv] using (A.comparison p z hz).1

end Yau.LeafProofs.L17Aux
