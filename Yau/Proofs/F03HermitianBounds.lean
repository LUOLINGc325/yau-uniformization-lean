import Yau.Blueprint.Analytic

/-! Elementary order operations for the project's actual Hermitian matrix inequalities. -/
noncomputable section
open scoped ComplexOrder Matrix
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem hermLE_refl (A : Herm n) : HermLE A A := by
  unfold HermLE
  simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : Herm n).PosSemidef)

theorem hermLE_trans {A B C : Herm n} (hAB : HermLE A B) (hBC : HermLE B C) : HermLE A C := by
  unfold HermLE at *
  convert hBC.add hAB using 1
  abel

theorem hermLE_add {A B C D : Herm n} (hAB : HermLE A B) (hCD : HermLE C D) :
    HermLE (A+C) (B+D) := by
  unfold HermLE at *
  convert hAB.add hCD using 1
  abel

theorem hermLE_real_smul {A B : Herm n} (hAB : HermLE A B) {c : ℝ} (hc : 0 ≤ c) :
    HermLE (Complex.ofReal c • A) (Complex.ofReal c • B) := by
  unfold HermLE at *
  simpa only [smul_sub] using hAB.smul (Complex.zero_le_real.mpr hc)

theorem hermLE_neg {A B : Herm n} (hAB : HermLE A B) : HermLE (-B) (-A) := by
  unfold HermLE at *
  convert hAB using 1
  abel

theorem hermLE_sum {ι : Type*} (S : Finset ι) (A B : ι → Herm n)
    (hAB : ∀ i ∈ S,HermLE (A i) (B i)) : HermLE (∑ i ∈ S,A i) (∑ i ∈ S,B i) := by
  classical
  unfold HermLE at *
  simpa only [Finset.sum_sub_distrib] using Matrix.posSemidef_sum S hAB

def HermAbsLE (A G : Herm n) (C : ℝ) : Prop :=
  HermLE (Complex.ofReal (-C) • G) A ∧ HermLE A (Complex.ofReal C • G)

theorem hermAbsLE_zero (G : Herm n) : HermAbsLE 0 G 0 := by
  constructor <;> simpa only [neg_zero,Complex.ofReal_zero,zero_smul] using hermLE_refl (0 : Herm n)

theorem hermAbsLE_add {A B G : Herm n} {C D : ℝ}
    (hA : HermAbsLE A G C) (hB : HermAbsLE B G D) : HermAbsLE (A+B) G (C+D) := by
  constructor
  · convert hermLE_add hA.1 hB.1 using 1 <;>
      simp only [Complex.ofReal_add,Complex.ofReal_neg,neg_add,add_smul]
  · convert hermLE_add hA.2 hB.2 using 1 <;>
      simp only [Complex.ofReal_add,add_smul]

theorem hermAbsLE_neg {A G : Herm n} {C : ℝ} (hA : HermAbsLE A G C) : HermAbsLE (-A) G C := by
  constructor
  · convert hermLE_neg hA.2 using 1 <;> simp only [Complex.ofReal_neg,neg_smul]
  · convert hermLE_neg hA.1 using 1 <;> simp only [Complex.ofReal_neg,neg_smul,neg_neg]

theorem hermAbsLE_nonneg_smul {A G : Herm n} {C c : ℝ} (hA : HermAbsLE A G C) (hc : 0 ≤ c) :
    HermAbsLE (Complex.ofReal c • A) G (c*C) := by
  constructor
  · convert hermLE_real_smul hA.1 hc using 1 <;>
      simp only [smul_smul,Complex.ofReal_mul,Complex.ofReal_neg,mul_neg]
  · convert hermLE_real_smul hA.2 hc using 1 <;> simp only [smul_smul,Complex.ofReal_mul]

theorem hermAbsLE_real_smul {A G : Herm n} {C : ℝ} (hA : HermAbsLE A G C) (c : ℝ) :
    HermAbsLE (Complex.ofReal c • A) G (|c| *C) := by
  by_cases hc : 0 ≤ c
  · simpa only [abs_of_nonneg hc] using hermAbsLE_nonneg_smul hA hc
  · have hNeg := hermAbsLE_neg (hermAbsLE_nonneg_smul hA (neg_nonneg.mpr (le_of_not_ge hc)))
    simpa only [Complex.ofReal_neg,neg_smul,neg_neg,abs_of_neg (lt_of_not_ge hc)] using hNeg

theorem hermAbsLE_mono {A G : Herm n} {C D : ℝ} (hG : G.PosSemidef)
    (hA : HermAbsLE A G C) (hCD : C ≤ D) : HermAbsLE A G D := by
  have hError := hG.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hCD))
  constructor
  · unfold HermLE at *
    convert hA.1.add hError using 1
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Complex.ofReal_sub,Complex.ofReal_neg]
    ring
  · unfold HermLE at *
    convert hA.2.add hError using 1
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub]
    ring

theorem hermAbsLE_sum {ι : Type*} (S : Finset ι) (A : ι → Herm n) (G : Herm n) (C : ι → ℝ)
    (hA : ∀ i ∈ S,HermAbsLE (A i) G (C i)) :
    HermAbsLE (∑ i ∈ S,A i) G (∑ i ∈ S,C i) := by
  constructor
  · convert hermLE_sum S _ _ (fun i hi => (hA i hi).1) using 1 <;>
      simp only [Complex.ofReal_sum,Finset.sum_smul,Finset.sum_neg_distrib,Complex.ofReal_neg,neg_smul]
  · convert hermLE_sum S _ _ (fun i hi => (hA i hi).2) using 1 <;>
      simp only [Complex.ofReal_sum,Finset.sum_smul]

end Yau.Proofs.F03Aux
