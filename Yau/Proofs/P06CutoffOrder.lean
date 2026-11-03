import Yau.Proofs.P06OrderAlgebra
import Yau.Proofs.P06CutoffData

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem formHermitianMatrix_multiply (η : M.Carrier → ℝ) (A : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (multiplyRealForm η A) x = (η x : ℂ) • formHermitianMatrix A x := by
  have he : formHermitianMatrix (multiplyRealForm η A) x = formHermitianMatrix ((η x) • A) x := rfl
  rw [he, G04Aux.formHermitianMatrix_real_smul]

theorem realOneOne_multiply (η : M.Carrier → ℝ) (A : RealForm M 2) (hA : RealOneOne A) :
    RealOneOne (multiplyRealForm η A) := by
  intro x u v
  change η x * A x ![Complex.I • u, Complex.I • v] = η x * A x ![u, v]
  rw [hA x u v]

/-- Multiplication by a scalar in [0,1] preserves the same signed paper
order bound, including C=0 and arbitrary nonclosed real (1,1) forms. -/
theorem formOrderBound_multiply (g : HermitianField M) (η : M.Carrier → ℝ)
    (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (A : RealForm M 2) {C : ℝ} (hC : 0 ≤ C)
    (hA : FormOrderBound g C A) : FormOrderBound g C (multiplyRealForm η A) := by
  intro x
  have hG := (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hCℂ : 0 ≤ (C : ℂ) := Complex.nonneg_iff.mpr ⟨hC, rfl⟩
  have haℂ : 0 ≤ (η x : ℂ) := Complex.nonneg_iff.mpr ⟨(hη x).1, rfl⟩
  have hbℂ : 0 ≤ ((1 - η x : ℝ) : ℂ) :=
    Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hη x).2, rfl⟩
  have hCG := hG.smul hCℂ
  have hL := ((hA x).1.smul haℂ).add (hCG.smul hbℂ)
  have hR := ((hA x).2.smul haℂ).add (hCG.smul hbℂ)
  rw [formHermitianMatrix_multiply]
  have heL : (η x : ℂ) • formHermitianMatrix A x - (-C : ℂ) • gMat g x =
      (η x : ℂ) • (formHermitianMatrix A x - (-C : ℂ) • gMat g x) +
        ((1 - η x : ℝ) : ℂ) • ((C : ℂ) • gMat g x) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have heR : (C : ℂ) • gMat g x - (η x : ℂ) • formHermitianMatrix A x =
      (η x : ℂ) • ((C : ℂ) • gMat g x - formHermitianMatrix A x) +
        ((1 - η x : ℝ) : ℂ) • ((C : ℂ) • gMat g x) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_one]
    ring
  exact ⟨heL ▸ hL, heR ▸ hR⟩

theorem boundedOneOneData_multiply (g : HermitianField M) (η : M.Carrier → ℝ)
    (hη : SmoothFn η) (hηrange : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (A : RealForm M 2) (hA : BoundedOneOneData g A) :
    BoundedOneOneData g (multiplyRealForm η A) := by
  obtain ⟨hs, h11, C, hC, hbound⟩ := hA
  exact ⟨smoothRealForm_multiply η A hη hs, realOneOne_multiply η A h11,
    C, hC, formOrderBound_multiply g η hηrange A hC hbound⟩

theorem metricCutoff_boundedOneOneData (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M 2) (hA : BoundedOneOneData g.form A) :
    ∀ j, 1 ≤ j → BoundedOneOneData g.form (fun x => χ j x • A x) := by
  obtain ⟨C, hC, hc⟩ := hχ
  intro j hj
  exact boundedOneOneData_multiply g.form (χ j) (hc j hj).1 ((hc j hj).2.2.1) A hA

end Yau.NodeProofs.P06Aux
