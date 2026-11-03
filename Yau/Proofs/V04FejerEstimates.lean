import Yau.Proofs.V04FejerColumnSeminorm

/-! The full original Fejer component: one constant precedes the disc,
frame, frequency, and test column. Error, closed-disc sup, and exact
Fourier-seminorm estimates use the same frozen polynomial. -/

open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem fejerEstimates_of_symbolBounds {d : VariationData X q} (hd : VariationSetup d)
    {a : ℕ} (ha : 4 ≤ a) (hsymbol : SymbolBounds d a) : FejerEstimates d a := by
  intro j
  obtain ⟨Cerr, hCerr, herr⟩ := negativeFejerError_bound hd ha hsymbol j
  obtain ⟨M, hM, hsymbolj⟩ := hsymbol j
  let r : ℝ := (2 * n : ℕ)
  have hr : 0 ≤ r := by positivity
  let C : ℝ := Cerr + 2 * r * M ^ 2 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCE : Cerr ≤ C := by
    have hx : 0 ≤ 2 * r * M ^ 2 := by positivity
    dsimp [C]
    linarith only [hx]
  have hC1 : 1 ≤ C := by
    have hx : 0 ≤ 2 * r * M ^ 2 := by positivity
    dsimp [C]
    linarith only [hCerr, hx]
  have hC2 : 2 * r * M ^ 2 ≤ C := by dsimp [C]; linarith only [hCerr]
  have hCx : r * M ^ 2 ≤ C := by
    have hx : 0 ≤ r * M ^ 2 := by positivity
    nlinarith only [hC2, hx]
  have hCsq : r * M ^ 2 ≤ C ^ 2 := hCx.trans (by
    have hh := mul_le_mul_of_nonneg_left hC1 hC
    simpa only [mul_one, pow_two] using hh)
  refine ⟨C, hC, fun F E hF hE P hP => ⟨?_, fun i => ?_⟩⟩
  · exact (herr F E hF hE P hP).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCE (by positivity)) (by positivity))
  · refine ⟨fejerTestColumn_holomorphic d j a F E P i,
      fejerTestColumn_zero d j a F E P i, ?_, ?_⟩
    · intro z hz
      exact (fejerTestColumn_closedDisc_bound hd ha hF hE hM
        (hsymbolj F E hF hE).1 P i z hz).trans hCsq
    · have hs := fejerTestColumn_boundaryDSq_bound hd ha hF hE hM
        (hsymbolj F E hF hE).1 P i
      apply hs.trans
      apply ENNReal.ofReal_le_ofReal
      change r * ((2 * P + 1 : ℝ) * M ^ 2) ≤ C * (P + 1)
      have hfirst : r * ((2 * P + 1 : ℝ) * M ^ 2) ≤ 2 * r * M ^ 2 * (P + 1) := by
        have hx : 0 ≤ r * M ^ 2 := by positivity
        nlinarith only [hx]
      exact hfirst.trans (mul_le_mul_of_nonneg_right hC2 (by positivity))

end Yau.Blueprint.V04Proof
