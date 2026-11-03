import Yau.Proofs.E01DetVariation
import Yau.Proofs.E01FeasibleCompact
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Determinant maximality gives the actual inverse-matrix trace support bound. -/

noncomputable section
open scoped Matrix ComplexOrder Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem minorant_nonnegative_combination
    (v : ComplexVector n → EReal) (A B : Herm n)
    (hAv : ∀ η, (ellipsoidQuadratic A η : EReal) ≤ v η)
    (hBv : ∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    ∀ η, (ellipsoidQuadratic ((r : ℂ) • A + (s : ℂ) • B) η : EReal) ≤ v η := by
  intro η
  rw [ellipsoidQuadratic_add, ellipsoidQuadratic_real_smul, ellipsoidQuadratic_real_smul]
  let M := max (ellipsoidQuadratic A η) (ellipsoidQuadratic B η)
  have hreal : r * ellipsoidQuadratic A η + s * ellipsoidQuadratic B η ≤ M := by
    calc
      _ ≤ r * M + s * M := add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hr)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hs)
      _ = M := by rw [← add_mul, hrs, one_mul]
  apply (EReal.coe_le_coe_iff.mpr hreal).trans
  rcases le_total (ellipsoidQuadratic A η) (ellipsoidQuadratic B η) with h | h
  · simpa only [M, max_eq_right h] using hBv η
  · simpa only [M, max_eq_left h] using hAv η

theorem matrix_convex_line (A B : Herm n) (s : ℝ) :
    A + (s : ℂ) • (B - A) = ((1 - s : ℝ) : ℂ) • A + (s : ℂ) • B := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem trace_inv_mul_le_dim_of_minorant_max
    (v : ComplexVector n → EReal) (A : Herm n) (hA : A.PosDef)
    (hAv : ∀ η, (ellipsoidQuadratic A η : EReal) ≤ v η)
    (hmax : ∀ B : Herm n, B.PosDef →
      (∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η) → B.det.re ≤ A.det.re)
    (D : Herm n) (hD : D.PosDef)
    (hDv : ∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) :
    (Matrix.trace (A⁻¹ * D)).re ≤ n := by
  let f : ℝ → ℝ := fun s => (A + (s : ℂ) • (D - A)).det.re
  have hf : HasDerivAt f (A.det.re * (Matrix.trace (A⁻¹ * (D - A))).re) 0 :=
    determinant_line_hasDerivAt A (D - A) hA
  have hlocal : IsLocalMaxOn f (Ici 0) 0 := by
    change ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, f s ≤ f 0
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs0 hs
    by_cases hz : s = 0
    · simp only [hz, le_refl]
    · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hz)
      have hs1 : s < 1 := hs.trans (by norm_num)
      have hpos : (((1 - s : ℝ) : ℂ) • A + (s : ℂ) • D).PosDef :=
        (hA.smul (Complex.zero_lt_real.mpr (sub_pos.mpr hs1))).add
          (hD.smul (Complex.zero_lt_real.mpr hsp))
      have hminorant := minorant_nonnegative_combination v A D hAv hDv
        (1 - s) s (sub_nonneg.mpr hs1.le) hs0 (by ring)
      have hh := hmax _ hpos hminorant
      change (A + (s : ℂ) • (D - A)).det.re ≤ (A + (0 : ℂ) • (D - A)).det.re
      rw [matrix_convex_line A D s]
      simpa only [zero_smul, add_zero] using hh
  have hdir : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simpa only [zero_add] using
      (convex_Ici (0 : ℝ)).segment_subset (by simp) (by simp)
  have hn : A.det.re * (Matrix.trace (A⁻¹ * (D - A))).re ≤ 0 := by
    simpa using hlocal.hasFDerivWithinAt_nonpos hf.hasFDerivAt.hasFDerivWithinAt hdir
  have hdet : 0 < A.det.re := (Complex.pos_iff.mp hA.det_pos).1
  have htrace : (Matrix.trace (A⁻¹ * (D - A))).re ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge hn) (mul_pos hdet (lt_of_not_ge h))
  have htr : (Matrix.trace (A⁻¹ * (D - A))).re =
      (Matrix.trace (A⁻¹ * D)).re - (n : ℝ) := by
    rw [Matrix.mul_sub, Matrix.trace_sub,
      Matrix.nonsing_inv_mul _ (hA.isUnit.map Matrix.detMonoidHom)]
    simp
  rw [htr] at htrace
  exact sub_nonpos.mp htrace

end Yau.NodeProofs.E01Aux
