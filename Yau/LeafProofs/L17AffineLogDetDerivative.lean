import Yau.LeafProofs.L07
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped Matrix.Norms.Elementwise ComplexOrder
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

theorem affine_matrix_det_hasDerivAt {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (hdet : IsUnit (G+t • E).det) :
    HasDerivAt (fun s : ℝ => (G+s • E).det)
      ((G+t • E).det*Matrix.trace ((G+t • E)⁻¹*E)) t := by
  let H : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s => G+s • E
  have hH : DifferentiableAt ℝ H t := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    change DifferentiableAt ℝ (fun s : ℝ => G i j+s • E i j) t
    fun_prop
  have hDeriv : fderiv ℝ H t 1=E := by
    ext i j
    rw [← L07Aux.matrix_fderiv_entry H t 1 hH i j]
    have he := (hasDerivAt_const t (G i j)).add ((hasDerivAt_id t).smul_const (E i j))
    simpa only [deriv,H,Pi.add_def,Matrix.add_apply,Matrix.smul_apply,zero_add,one_smul,Function.id_def] using he.deriv
  have hD := (((L07Aux.determinantMultilinear n).hasFDerivAt (H t)).restrictScalars ℝ).comp t hH.hasFDerivAt
  convert hD.differentiableAt.hasDerivAt using 1
  · rfl
  · change _=fderiv ℝ (fun s => (H s).det) t 1
    rw [L07Aux.determinant_fderiv_trace H t 1 hH hdet,hDeriv]


theorem affine_logDet_hasDerivAt {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (hpos : (G+t • E).PosDef) :
    HasDerivAt (fun s : ℝ => Real.log (G+s • E).det.re)
      (Matrix.trace ((G+t • E)⁻¹*E)).re t := by
  have hdetR := (Complex.pos_iff.mp hpos.det_pos).1
  have hdetI := (Complex.pos_iff.mp hpos.det_pos).2.symm
  have hd := affine_matrix_det_hasDerivAt G E t (isUnit_iff_ne_zero.mpr hpos.det_pos.ne')
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have hl := hr.log hdetR.ne'
  convert hl using 1
  · rfl
  · change _=((G+t • E).det*Matrix.trace ((G+t • E)⁻¹*E)).re/(G+t • E).det.re
    rw [Complex.mul_re,hdetI,zero_mul,sub_zero]
    field_simp [hdetR.ne']

theorem matrixRealScalar_eq_complexScalar (s : ℝ) (E : Matrix (Fin n) (Fin n) ℂ) :
    s • E=(s : ℂ) • E := by
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]

end Yau.LeafProofs.L17Aux
