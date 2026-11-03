import spec.CHAIN.CONTRACTS

/-! Uncompiled F01 scratch: the actual positive Hermitian field exp(f)g.
No SmoothMetric record is manufactured: its Kähler equations generally fail
for this conformal field. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def conformalInnerProduct (c : ℝ) (h : Yau.HermitianInnerProduct V) :
    Yau.HermitianInnerProduct V where
  toFun u v := (Real.exp c : ℂ) * h.toFun u v
  map_add_left u₁ u₂ v := by rw [h.map_add_left, mul_add]
  map_smul_left a u v := by rw [h.map_smul_left]; ring
  map_add_right u v₁ v₂ := by rw [h.map_add_right, mul_add]
  map_smul_right a u v := by rw [h.map_smul_right]; ring
  conjugate_symmetric u v := by
    change (Real.exp c : ℂ) * h.toFun u v =
      (starRingEnd ℂ) ((Real.exp c : ℂ) * h.toFun v u)
    rw [map_mul, Complex.conj_ofReal]
    exact congrArg ((Real.exp c : ℂ) * ·) (h.conjugate_symmetric u v)
  self_adjoint u := by simp [Complex.mul_im, h.self_adjoint u]
  positive_definite u := by
    have he : 0 < Real.exp c := Real.exp_pos c
    have hval : ((Real.exp c : ℂ) * h.toFun u u).re =
        Real.exp c * (h.toFun u u).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hval]
    exact ⟨mul_nonneg he.le (h.positive_definite u).1,
      by rw [mul_eq_zero, or_iff_right he.ne', (h.positive_definite u).2]⟩

variable {n : ℕ} {M : Yau.ComplexManifold n}

def conformalField (h : Yau.HermitianField M) (f : M.Carrier → ℝ) :
    Yau.HermitianField M := fun x => conformalInnerProduct (f x) (h x)

theorem conformalField_value (h : Yau.HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) (u v : Yau.TangentVector M x) :
    (conformalField h f x).toFun u v = (Real.exp (f x) : ℂ) * (h x).toFun u v := rfl

theorem conformalField_hMat (h : Yau.HermitianField M) (f : M.Carrier → ℝ)
    (a : M.Carrier) (z : Yau.ComplexVector n) :
    Yau.hMat (conformalField h f) a z =
      (Real.exp (f (Yau.chartInv a z)) : ℂ) • Yau.hMat h a z := rfl

theorem conformalField_gMat (h : Yau.HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) :
    Yau.gMat (conformalField h f) x = (Real.exp (f x) : ℂ) • Yau.gMat h x := by
  rw [Yau.gMat, conformalField_hMat]
  simp [Yau.gMat, Yau.chartInv, Yau.chartPt]

theorem conformalField_hMat_det (h : Yau.HermitianField M) (f : M.Carrier → ℝ)
    (a : M.Carrier) (z : Yau.ComplexVector n) :
    (Yau.hMat (conformalField h f) a z).det =
      (Real.exp (f (Yau.chartInv a z)) : ℂ) ^ n * (Yau.hMat h a z).det := by
  rw [conformalField_hMat, Matrix.det_smul]
  simp only [Fintype.card_fin]

end Yau.NodeProofs.F01Aux
