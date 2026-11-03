import Yau.Proofs.V03Fourier

/-! Conjugation reverses native circle Fourier modes. -/

open scoped Topology ComplexConjugate
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem fourierCoeff_conj (u : AddCircle T → ℂ) (k : ℤ) :
    fourierCoeff (fun x => conj (u x)) k = conj (fourierCoeff u (-k)) := by
  unfold fourierCoeff
  simp only [neg_neg, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  simp only [map_mul, ← fourier_neg]

theorem fourierCoeff_real_neg (u : AddCircle T → ℝ) (k : ℤ) :
    fourierCoeff (fun x => (u x : ℂ)) (-k) =
      conj (fourierCoeff (fun x => (u x : ℂ)) k) := by
  have hh := fourierCoeff_conj (fun x => (u x : ℂ)) (-k)
  simpa only [Complex.conj_ofReal, neg_neg] using hh

end Yau.Blueprint.V03Proof
