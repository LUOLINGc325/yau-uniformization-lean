import Yau.Proofs.P06HermitianTestDecomposition

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux

theorem polarizationCoefficients_contDiff {n : ℕ} {F : ComplexVector n → ℂ}
    (hF : ContDiff ℝ ∞ F) (r : Fin 4) :
    ContDiff ℝ ∞ (fun z => polarizationCoefficients (F z) r) := by
  have hr := Complex.reCLM.contDiff.comp hF
  have hi := Complex.imCLM.contDiff.comp hF
  fin_cases r
  · exact hr.div_const 4
  · exact hr.neg.div_const 4
  · exact hi.neg.div_const 4
  · exact hi.div_const 4

theorem polarizationCoefficients_zero (r : Fin 4) : polarizationCoefficients 0 r = 0 := by
  fin_cases r <;> norm_num [polarizationCoefficients]

theorem hermitianTestCoefficients_regular {n : ℕ} {O : Set (ComplexVector n)}
    (B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun z => B z i j))
    (hcB : ∀ i j, HasCompactSupport (fun z => B z i j))
    (hBO : ∀ i j, tsupport (fun z => B z i j) ⊆ O)
    (p : (Fin n × Fin n) × Fin 4) :
    ContDiff ℝ ∞ (fun z => hermitianTestCoefficients (B z) p) ∧
      HasCompactSupport (fun z => hermitianTestCoefficients (B z) p) ∧
      tsupport (fun z => hermitianTestCoefficients (B z) p) ⊆ O := by
  let F : ComplexVector n → ℂ := fun z => B z p.1.1 p.1.2
  let q : ℂ → ℝ := fun c => polarizationCoefficients c p.2
  have hq : q 0 = 0 := polarizationCoefficients_zero p.2
  have hs : tsupport (q ∘ F) ⊆ tsupport F := tsupport_comp_subset hq F
  refine ⟨polarizationCoefficients_contDiff (hB p.1.1 p.1.2) p.2, ?_, hs.trans (hBO _ _)⟩
  exact (hcB p.1.1 p.1.2).of_isClosed_subset (isClosed_tsupport _) hs

def leviMatrixTestDual {n : ℕ} (B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (z : ComplexVector n) : ℝ :=
  ∑ p, leviDirection (leviC (fun w => hermitianTestCoefficients (B w) p) z)
    (hermitianTestVectors n p)

theorem leviMatrixTestDual_integral {n : ℕ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (u : ComplexVector n → ℝ) (hu : ContinuousOn u O)
    (B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hreg : ∀ p : (Fin n × Fin n) × Fin 4,
      ContDiff ℝ ∞ (fun z => hermitianTestCoefficients (B z) p) ∧
      HasCompactSupport (fun z => hermitianTestCoefficients (B z) p) ∧
      tsupport (fun z => hermitianTestCoefficients (B z) p) ⊆ O) :
    (∫ z, u z * leviMatrixTestDual B z ∂lebesgueC n) =
      ∑ p, ∫ z, u z * leviDirection
        (leviC (fun z => hermitianTestCoefficients (B z) p) z)
        (hermitianTestVectors n p) ∂lebesgueC n := by
  have : (lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]; infer_instance
  simp only [leviMatrixTestDual, Finset.mul_sum]
  apply integral_finsetSum
  intro p _
  have hq := contDiffOn_univ.mp (leviDirection_contDiffOn isOpen_univ
    (hreg p).1.contDiffOn (hermitianTestVectors n p))
  obtain ⟨hcq, hqφ⟩ := leviDirection_hasCompactSupport
    (fun z => hermitianTestCoefficients (B z) p) (hreg p).2.1 (hermitianTestVectors n p)
  simpa only [mul_comm] using
    integrable_compactTest_mul (lebesgueC n) hO hq.continuous hcq (hqφ.trans (hreg p).2.2) hu

theorem hermitianTest_metric_integral {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier)
    (B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) (hBH : ∀ z, (B z).IsHermitian)
    (hreg : ∀ p : (Fin n × Fin n) × Fin 4,
      ContDiff ℝ ∞ (fun z => hermitianTestCoefficients (B z) p) ∧
      HasCompactSupport (fun z => hermitianTestCoefficients (B z) p) ∧
      tsupport (fun z => hermitianTestCoefficients (B z) p) ⊆ chartTarget x) :
    (∑ p, ∫ z, hermitianTestCoefficients (B z) p *
      leviDirection (hMat g.form x z) (hermitianTestVectors n p) ∂lebesgueC n) =
        ∫ z, (Matrix.trace (hMat g.form x z * B z)).re ∂lebesgueC n := by
  have : (lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]; infer_instance
  rw [← integral_finsetSum _ (fun p _ =>
    integrable_compactTest_mul (lebesgueC n)
      (isOpen_extChartAt_target (I := ComplexModel n) x) (hreg p).1.continuous
      (hreg p).2.1 (hreg p).2.2
      (metricLeviDirection_contDiffOn g x (hermitianTestVectors n p)).continuousOn)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← trace_rankOne_family, hermitianTestDecomposition (B z) (hBH z)]

/-- The literal weak Levi inequality controls every compact smooth positive
Hermitian matrix test, using a fixed finite family of constant directions
and scalar coefficients of either sign. -/
theorem weakLeviUpper_positive_matrix_test {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (hf : Continuous f) (C : ℝ)
    (hc : ConstantOutsideCompact f) (hw : WeakLeviUpper g.form f C) (x : M.Carrier)
    (B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun z => B z i j))
    (hcB : ∀ i j, HasCompactSupport (fun z => B z i j))
    (hBO : ∀ i j, tsupport (fun z => B z i j) ⊆ chartTarget x)
    (hpB : ∀ z, (B z).PosSemidef) :
    (∫ z, inChart x f z * leviMatrixTestDual B z ∂lebesgueC n) ≤
      C * ∫ z, (Matrix.trace (hMat g.form x z * B z)).re ∂lebesgueC n := by
  have hreg := hermitianTestCoefficients_regular B hB hcB hBO
  have hu : ContinuousOn (inChart x f) (chartTarget x) :=
    hf.comp_continuousOn (continuousOn_extChartAt_symm (I := ComplexModel n) x)
  rw [leviMatrixTestDual_integral (isOpen_extChartAt_target (I := ComplexModel n) x)
      (inChart x f) hu B hreg,
    ← hermitianTest_metric_integral g x B (fun z => (hpB z).1) hreg]
  apply weakLeviUpper_positive_family g f hf C hc hw x (hermitianTestVectors n)
    (fun p z => hermitianTestCoefficients (B z) p)
    (fun p => (hreg p).1) (fun p => (hreg p).2.1) (fun p => (hreg p).2.2)
  intro z
  rw [hermitianTestDecomposition (B z) (hpB z).1]
  exact hpB z

end Yau.NodeProofs.P06Aux
