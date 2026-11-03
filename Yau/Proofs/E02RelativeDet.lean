import Yau.Proofs.E02SpectralLogdet
import Yau.Proofs.G04Whitening
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open Matrix Set
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Eigenvalues above one are individually bounded by their actual
product. No eigenbasis is selected as a function of parameters. -/
theorem one_le_posDef_le_det_smul_one {n : ℕ} (C : Herm n) (hC : C.PosDef)
    (hOne : (C-1).PosSemidef) : ((C.det.re:ℂ) • (1:Herm n)-C).PosSemidef := by
  have hLower : algebraMap ℝ (Herm n) 1 ≤ C := by
    apply Matrix.le_iff.mpr
    simpa only [map_one] using hOne
  have hSpectrum := (algebraMap_le_iff_le_spectrum (R := ℝ) hC.isHermitian.isSelfAdjoint).mp hLower
  have hEigOne : ∀ i, 1 ≤ hC.isHermitian.eigenvalues i :=
    fun i => hSpectrum _ (hC.isHermitian.eigenvalues_mem_spectrum_real i)
  have hEigUpper : ∀ i, hC.isHermitian.eigenvalues i ≤ C.det.re := by
    intro i
    have hb := Finset.le_prod_max_one (Finset.mem_univ i) hC.isHermitian.eigenvalues
    have hProd : (∏ j, max (hC.isHermitian.eigenvalues j) 1) = ∏ j, hC.isHermitian.eigenvalues j :=
      Finset.prod_congr rfl (fun j _ => max_eq_left (hEigOne j))
    rw [hProd] at hb
    rw [(posDef_spectral_det_trace C hC).1]
    exact hb
  have hUpper : C ≤ algebraMap ℝ (Herm n) C.det.re := by
    apply (le_algebraMap_iff_spectrum_le (R := ℝ) hC.isHermitian.isSelfAdjoint).mpr
    intro r hr
    rw [hC.isHermitian.spectrum_real_eq_range_eigenvalues] at hr
    obtain ⟨i,rfl⟩ := hr
    exact hEigUpper i
  have hAlg : algebraMap ℝ (Herm n) C.det.re = (C.det.re:ℂ) • (1:Herm n) := by
    ext i j
    simp [Algebra.algebraMap_eq_smul_one,Matrix.smul_apply,Complex.real_smul]
  simpa only [hAlg] using Matrix.le_iff.mp hUpper

/-- The exact relative determinant order used only on a PSD majorant. -/
theorem posDef_relative_det_order {n : ℕ} (B b : Herm n) (hB : B.PosDef) (hb : b.PosDef)
    (hOrder : (b-B).PosSemidef) :
    (((b.det.re/B.det.re:ℝ):ℂ) • B-b).PosSemidef := by
  obtain ⟨S,hS,hu,hSS,hSBS⟩ := G04Aux.exists_hermitian_whitening B hB
  let C : Herm n := S*b*S
  have hC : C.PosDef := by
    have hh := hb.conjTranspose_mul_mul_same (B := S) (Matrix.mulVec_injective_of_isUnit hu)
    simpa only [hS.eq] using hh
  have hCI : (C-1).PosSemidef := by
    have hh := hOrder.conjTranspose_mul_mul_same S
    simpa only [hS.eq,Matrix.mul_sub,Matrix.sub_mul,hSBS] using hh
  have hCU := one_le_posDef_le_det_smul_one C hC hCI
  have hConj := hu.posSemidef_star_left_conjugate_iff (x := (C.det.re:ℂ) • B-b)
  rw [hS.star_eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hSBS] at hConj
  have hRaw : ((C.det.re:ℂ) • B-b).PosSemidef := hConj.mp hCU
  have hSSDet : S.det*S.det*B.det = 1 := by
    rw [←Matrix.det_mul,hSS]
    exact Matrix.det_nonsing_inv_mul_det (A := B) (hB.isUnit.map Matrix.detMonoidHom)
  have hDet : C.det*B.det = b.det := by
    change (S*b*S).det*B.det = b.det
    rw [Matrix.det_mul,Matrix.det_mul]
    calc
      _ = b.det*(S.det*S.det*B.det) := by ring
      _ = b.det := by rw [hSSDet,mul_one]
  have hBPos : 0 < B.det.re := (RCLike.pos_iff.mp hB.det_pos).1
  have hBIm : B.det.im = 0 := (RCLike.pos_iff.mp hB.det_pos).2
  have hDetRe := congrArg Complex.re hDet
  simp only [Complex.mul_re,hBIm,mul_zero,sub_zero] at hDetRe
  have hRatio : C.det.re = b.det.re/B.det.re := (eq_div_iff hBPos.ne').mpr hDetRe
  rw [hRatio] at hRaw
  exact hRaw

end Yau.NodeProofs.E02Aux
