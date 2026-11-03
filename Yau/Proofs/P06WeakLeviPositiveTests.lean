import Yau.Proofs.P06LeviMatrixTests

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux

/-- The original constant-direction weak inequality controls every finite
signed family of compact smooth tests whose combined Hermitian matrix is
pointwise positive. Individual scalar coefficients need not be positive. -/
theorem weakLeviUpper_positive_family {n : ℕ} {M : ComplexManifold n}
    {ι : Type*} [Fintype ι] (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : Continuous f) (C : ℝ) (hc : ConstantOutsideCompact f)
    (hw : WeakLeviUpper g.form f C) (x : M.Carrier)
    (v : ι → ComplexVector n) (φ : ι → ComplexVector n → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hcφ : ∀ i, HasCompactSupport (φ i))
    (hφO : ∀ i, tsupport (φ i) ⊆ chartTarget x)
    (hp : ∀ z, (∑ i, (φ i z : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp (v i)) (star (WithLp.ofLp (v i)))).PosSemidef) :
    (∑ i, ∫ z, inChart x f z * leviDirection (leviC (φ i) z) (v i) ∂lebesgueC n) ≤
      C * ∑ i, ∫ z, φ i z * leviDirection (hMat g.form x z) (v i) ∂lebesgueC n := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let K : Set (ComplexVector n) := ⋃ i, tsupport (φ i)
  have hK : IsCompact K := isCompact_iUnion hcφ
  have hKO : K ⊆ chartTarget x := Set.iUnion_subset hφO
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hC : 0 ≤ C := weakLeviUpper_constantOutside_nonnegative g f C hc hw
  have hu : ContinuousOn (inChart x f) (chartTarget x) :=
    hf.comp_continuousOn (continuousOn_extChartAt_symm (I := ComplexModel n) x)
  let q (i : ι) (z : ComplexVector n) := leviDirection (leviC (φ i) z) (v i)
  have hq (i : ι) : Continuous (q i) :=
    (contDiffOn_univ.mp (leviDirection_contDiffOn isOpen_univ (hφ i).contDiffOn (v i))).continuous
  have hcq (i : ι) : HasCompactSupport (q i) :=
    (leviDirection_hasCompactSupport (φ i) (hcφ i) (v i)).1
  have hqφ (i : ι) : tsupport (q i) ⊆ tsupport (φ i) :=
    (leviDirection_hasCompactSupport (φ i) (hcφ i) (v i)).2
  have hqK (i : ι) : tsupport (q i) ⊆ K :=
    (hqφ i).trans (Set.subset_iUnion (fun i => tsupport (φ i)) i)
  let G : ℝ := ∑ i, ∫ z, φ i z * leviDirection (hMat g.form x z) (v i) ∂lebesgueC n
  let D : ℝ := ∑ i, ∫ z, |q i z| ∂lebesgueC n
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => integral_nonneg (fun z => abs_nonneg _))
  have hiG (i : ι) : Integrable (fun z => φ i z * leviDirection (hMat g.form x z) (v i)) (lebesgueC n) :=
    integrable_compactTest_mul (lebesgueC n) hO (hφ i).continuous (hcφ i) (hφO i)
      (metricLeviDirection_contDiffOn g x (v i)).continuousOn
  have hG : 0 ≤ G := by
    dsimp only [G]
    rw [← integral_finsetSum _ (fun i _ => hiG i)]
    apply integral_nonneg
    intro z
    change 0 ≤ ∑ i, φ i z * leviDirection (hMat g.form x z) (v i)
    by_cases hz : z ∈ K
    · rw [← trace_rankOne_family]
      exact matrix_trace_mul_nonneg _ _
        (Yau.LeafProofs.L12Aux.hMat_posDef g.form x z (hKO hz)).posSemidef (hp z)
    · have hzero (i : ι) : φ i z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hi => hz (Set.mem_iUnion.mpr ⟨i, hi⟩))
      simp only [hzero, zero_mul, Finset.sum_const_zero, le_refl]
  have hCG : 0 ≤ C * G := mul_nonneg hC hG
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (2 * (D + 1))
  let η : ℝ := ε / (2 * (C * G + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨U, hU, he, hb⟩ := weakLeviUpper_local_approximation g f hf C hc hw x K hK hKO δ η hδ hη
  have herror (i : ι) :
      (∫ z, inChart x f z * q i z ∂lebesgueC n) ≤
        (∫ z, U z * q i z ∂lebesgueC n) + δ * ∫ z, |q i z| ∂lebesgueC n := by
    have herr := integral_test_error_bound hO hu hU.continuous (hq i) (hcq i)
      ((hqφ i).trans (hφO i)) (hqK i) hδ.le he
    have hle := (le_abs_self _).trans herr
    linarith
  have hsumerror := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => herror i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumerror
  have hiU (i : ι) : Integrable (fun z => φ i z * leviDirection (leviC U z) (v i)) (lebesgueC n) := by
    have hcont := (hφ i).continuous.mul
      (contDiffOn_univ.mp (leviDirection_contDiffOn isOpen_univ hU.contDiffOn (v i))).continuous
    exact hcont.integrable_of_hasCompactSupport (hcφ i).mul_right
  have hpoint (z : ComplexVector n) :
      (∑ i, φ i z * leviDirection (leviC U z) (v i)) ≤
        C * (1 + η) * ∑ i, φ i z * leviDirection (hMat g.form x z) (v i) := by
    by_cases hz : z ∈ K
    · have h := rankOne_family_quadratic_order (leviC U z)
        (((C * (1 + η) : ℝ) : ℂ) • hMat g.form x z) (fun i => φ i z) v (hb z hz) (hp z)
      simpa only [leviDirection, Matrix.smul_mulVec, dotProduct_smul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul,
        Finset.mul_sum, mul_left_comm, mul_assoc] using h
    · have hzero (i : ι) : φ i z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hi => hz (Set.mem_iUnion.mpr ⟨i, hi⟩))
      simp only [hzero, zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  have hbound : (∑ i, ∫ z, U z * q i z ∂lebesgueC n) ≤ C * (1 + η) * G := by
    simp_rw [q, integral_leviDirection_test hO (hφ _) (hcφ _) (hφO _) hU.contDiffOn]
    dsimp only [G]
    rw [← integral_finsetSum _ (fun i _ => hiU i),
      ← integral_finsetSum _ (fun i _ => hiG i), ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ (fun i _ => hiU i))
      ((integrable_finsetSum _ (fun i _ => hiG i)).const_mul _) hpoint
  have hδeq : δ * (2 * (D + 1)) = ε := by
    dsimp only [δ]
    exact div_mul_cancel₀ ε (by positivity)
  have hηeq : η * (2 * (C * G + 1)) = ε := by
    dsimp only [η]
    exact div_mul_cancel₀ ε (by positivity)
  change (∑ i, ∫ z, inChart x f z * q i z ∂lebesgueC n) ≤ C * G + ε
  change (∑ i, ∫ z, inChart x f z * q i z ∂lebesgueC n) ≤
    (∑ i, ∫ z, U z * q i z ∂lebesgueC n) + δ * D at hsumerror
  nlinarith

end Yau.NodeProofs.P06Aux
