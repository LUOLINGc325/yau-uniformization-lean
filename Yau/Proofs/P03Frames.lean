import Yau.Proofs.P03Jets

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem tangentCoords_chartVec (p x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) p).source) (v : ComplexVector n) :
    tangentCoords p x (chartVec p x v) = v := by
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := ComplexModel n) hx
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  exact congrArg (fun L => L v) h

theorem chartVec_tangentCoords (p x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) p).source) (v : TangentVector M x) :
    chartVec p x (tangentCoords p x v) = v := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := ComplexModel n) hx
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  exact congrArg (fun L => L v) h

theorem jetAgreeFn_value {f : M.Carrier → ℂ} {p : M.Carrier}
    {P : MvPolynomial (Fin n) ℂ} {k : ℕ} (hf : JetAgreeFn f p P k) :
    f p = MvPolynomial.constantCoeff P := by
  have h := DFunLike.congr_fun (hf 0 (Nat.zero_le k)) (0 : Fin 0 → ComplexVector n)
  have hz : f p - MvPolynomial.constantCoeff P = 0 := by
    simpa [iteratedFDeriv_zero_apply, inChart, chartInv, chartPt,
      extChartAt_to_inv] using h
  exact sub_eq_zero.mp hz

theorem jetAgreeField_value {V : VectorField M} {p : M.Carrier}
    {P : Fin n → MvPolynomial (Fin n) ℂ} {k : ℕ} (hV : JetAgreeField V p P k) :
    tangentCoords p p (V p) = WithLp.toLp 2 (fun i => MvPolynomial.constantCoeff (P i)) := by
  have h := DFunLike.congr_fun (hV 0 (Nat.zero_le k)) (0 : Fin 0 → ComplexVector n)
  have hi : chartInv p (chartPt p p) = p := extChartAt_to_inv (I := ComplexModel n) p
  change fieldCoords V p (chartPt p p) - WithLp.toLp 2
    (fun i => MvPolynomial.eval (fun l => chartPt p p l - chartPt p p l) (P i)) = 0 at h
  unfold fieldCoords at h
  rw [hi] at h
  have hz : tangentCoords p p (V p) -
      WithLp.toLp 2 (fun i => MvPolynomial.constantCoeff (P i)) = 0 := by
    simpa using h
  exact sub_eq_zero.mp hz

/-- The actual local polynomial field, obtained by differentiating the inverse
chart rather than identifying tangent fibres by an arbitrary global frame. -/
def polynomialFieldInChart (p : M.Carrier)
    (P : Fin n → MvPolynomial (Fin n) ℂ) : VectorField M := fun x =>
  chartVec p x (WithLp.toLp 2 (fun i =>
    MvPolynomial.eval (fun l => chartPt p x l - chartPt p p l) (P i)))

theorem fieldCoords_polynomialFieldInChart (p : M.Carrier)
    (P : Fin n → MvPolynomial (Fin n) ℂ) {z : ComplexVector n} (hz : z ∈ chartTarget p) :
    fieldCoords (polynomialFieldInChart p P) p z =
      WithLp.toLp 2 (fun i => MvPolynomial.eval (fun l => z l - chartPt p p l) (P i)) := by
  have hx : chartInv p z ∈ (extChartAt (ComplexModel n) p).source :=
    (extChartAt (ComplexModel n) p).map_target hz
  have hinv : chartPt p (chartInv p z) = z :=
    (extChartAt (ComplexModel n) p).right_inv hz
  simp only [fieldCoords, polynomialFieldInChart, tangentCoords_chartVec p _ hx, hinv]

theorem polynomialFieldInChart_jet (p : M.Carrier)
    (P : Fin n → MvPolynomial (Fin n) ℂ) (k : ℕ) :
    JetAgreeField (polynomialFieldInChart p P) p P k := by
  have ht : chartTarget p ∈ 𝓝 (chartPt p p) := by
    simpa [chartTarget, chartPt, ComplexModel] using
      extChartAt_target_mem_nhdsWithin (I := ComplexModel n) p
  exact jetAgreeField_of_polynomial_germ
    (Filter.eventually_of_mem ht fun z hz => fieldCoords_polynomialFieldInChart p P hz) k

end Yau.NodeProofs.P03Aux
