import Yau.Proofs.B01Estimates

open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def frameVector (a : M.Carrier) (z : ComplexVector 1) (U : Fin r → ℂ) : E (chartInv a z) :=
  (BundleDbar.localTriv (r := r) E a).symmL ℂ (chartInv a z) (WithLp.toLp 2 U)

theorem frameVector_coordinates (a : M.Carrier) (z : ComplexVector 1)
    (hz : z ∈ BundleDbar.localDomain (r := r) E a) (U : Fin r → ℂ) :
    (BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z)
      (frameVector E a z U) = WithLp.toLp 2 U :=
  Trivialization.continuousLinearMapAt_symmL _ hz.2 _

theorem framePairing_section (k : BundleDbar.Metric E) (s : Section E)
    (a : M.Carrier) (z : ComplexVector 1) (hz : z ∈ BundleDbar.localDomain (r := r) E a)
    (U : Fin r → ℂ) :
    (∑ α, ∑ β, star (sectionCoefficients (r := r) E s a z α) *
      BundleDbar.metricMatrix (r := r) E k a z α β * U β) =
        (k (chartInv a z)).toFun (s (chartInv a z)) (frameVector E a z U) := by
  have he := LeafProofs.L14Aux.metricMatrix_pairing (r := r) E k a z hz
    (s (chartInv a z)) (frameVector E a z U)
  rw [frameVector_coordinates E a z hz U] at he
  exact he

theorem framePairing_normSq (k : BundleDbar.Metric E) (a : M.Carrier) (z : ComplexVector 1)
    (hz : z ∈ BundleDbar.localDomain (r := r) E a) (U : Fin r → ℂ) :
    (∑ α, ∑ β, BundleDbar.metricMatrix (r := r) E k a z α β * star (U α) * U β).re =
      hermitianNormSq (k (chartInv a z)) (frameVector E a z U) := by
  have he := LeafProofs.L14Aux.metricMatrix_pairing (r := r) E k a z hz
    (frameVector E a z U) (frameVector E a z U)
  rw [frameVector_coordinates E a z hz U] at he
  have hc : (∑ α, ∑ β, BundleDbar.metricMatrix (r := r) E k a z α β * star (U α) * U β) =
      ∑ α, ∑ β, star (U α) * BundleDbar.metricMatrix (r := r) E k a z α β * U β := by
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [hc, he]
  rfl

theorem cutoff_coefficient_quadratic_bound (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (φ χ : M.Carrier → ℝ)
    (hG : BundleDbar.GriffithsNonnegative (r := r) E k) (hφ : SmoothFn φ)
    (hl : ∀ x, 0 < discLeviScalar c φ x) (s : Section E)
    (a : M.Carrier) (z : ComplexVector 1) (hz : z ∈ BundleDbar.localDomain (r := r) E a)
    (U : Fin 1 → Fin r → ℂ) :
    2 * (LeafProofs.matrixCoefficientPairing (BundleDbar.metricMatrix (r := r) E k a z)
      (fun i α => BundleDbar.coefficients (r := r) E (cutoffSourceForm E c s χ) a z (fun _ => i) α) U).re -
        BundleDbar.nakanoQuadratic (BundleDbar.weightedCurvature (r := r) E k φ a z) U ≤
      Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)) *
        (hermitianNormSq (k (chartInv a z)) (s (chartInv a z)) *
          ‖discDbarScalar c χ (chartInv a z)‖ ^ 2 / discLeviScalar c φ (chartInv a z)) := by
  let H := BundleDbar.metricMatrix (r := r) E k a z
  let R := BundleDbar.curvature (r := r) E k a z 0 0
  let b := discDbarScalar c χ (chartInv a z)
  let d := Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0))
  let l := discLeviScalar c φ (chartInv a z)
  let v := frameVector E a z (U 0)
  let Q (B : Matrix (Fin r) (Fin r) ℂ) : ℂ := ∑ α, ∑ β, B α β * star (U 0 α) * U 0 β
  have hF : (fun i α => BundleDbar.coefficients (r := r) E (cutoffSourceForm E c s χ) a z (fun _ => i) α) =
      fun (_ : Fin 1) α => (b * (d : ℂ)) * sectionCoefficients (r := r) E s a z α := by
    funext i α
    exact congrArg (fun t : ComplexVector r => t α)
      (cutoffSourceForm_coefficients_normSq E c hc s χ a z hz (fun _ => i))
  have hpair : LeafProofs.matrixCoefficientPairing H
      (fun i α => BundleDbar.coefficients (r := r) E (cutoffSourceForm E c s χ) a z (fun _ => i) α) U =
      (d : ℂ) * (star b * (k (chartInv a z)).toFun (s (chartInv a z)) v) := by
    rw [hF, ← framePairing_section E k s a z hz (U 0)]
    unfold LeafProofs.matrixCoefficientPairing
    simp only [Fin.sum_univ_one, star_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hR : 0 ≤ (Q R).re := by
    simpa [BundleDbar.griffithsQuadratic, stdVec, Q, R] using
      hG a z hz (stdVec 0) (WithLp.toLp 2 (U 0))
  have hlev : leviC (inChart a φ) z 0 0 = ((l * d : ℝ) : ℂ) :=
    discLevi_inChart (r := r) E c hc φ hφ a hz.1
  have hsum : (∑ α : Fin r, ∑ β : Fin r,
      (R α β + ((l * d : ℝ) : ℂ) * H α β) * star (U 0 α) * U 0 β) =
        Q R + ((l * d : ℝ) : ℂ) * Q H := by
    simp only [Q, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hcurv : BundleDbar.nakanoQuadratic (BundleDbar.weightedCurvature (r := r) E k φ a z) U =
      (Q R).re + l * d * hermitianNormSq (k (chartInv a z)) v := by
    unfold BundleDbar.nakanoQuadratic BundleDbar.weightedCurvature
    simp only [Fin.sum_univ_one, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hlev]
    rw [hsum]
    change _ = (Q R).re + l * d * _
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [framePairing_normSq E k a z hz (U 0)]
  rw [hpair, hcurv]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hs := hermitian_square_bound (k (chartInv a z)) (s (chartInv a z)) v b l (hl _)
  have hb := mul_le_mul_of_nonneg_left hs (Complex.normSq_nonneg
    (wirt (fun w => c (chartInv a w)) z (stdVec 0)))
  change d * (2 * (star b * (k (chartInv a z)).toFun (s (chartInv a z)) v).re -
    l * hermitianNormSq (k (chartInv a z)) v) ≤
      d * (hermitianNormSq (k (chartInv a z)) (s (chartInv a z)) * ‖b‖ ^ 2 / l) at hb
  change 2 * (d * (star b * (k (chartInv a z)).toFun (s (chartInv a z)) v).re) -
    ((Q R).re + l * d * hermitianNormSq (k (chartInv a z)) v) ≤
      d * (hermitianNormSq (k (chartInv a z)) (s (chartInv a z)) * ‖b‖ ^ 2 / l)
  nlinarith only [hb, hR]

theorem cutoff_inverse_point_bound (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (φ χ : M.Carrier → ℝ)
    (hG : BundleDbar.GriffithsNonnegative (r := r) E k) (hφ : SmoothFn φ)
    (hl : ∀ x, 0 < discLeviScalar c φ x) (s : Section E) (x : M.Carrier) :
    BundleDbar.inverseCurvatureNormSq (r := r) E (flatDiscField c hc) k φ (cutoffSourceForm E c s χ) x ≤
      ENNReal.ofReal (hermitianNormSq (k x) (s x) * ‖discDbarScalar c χ x‖ ^ 2 / discLeviScalar c φ x) := by
  let d : ℝ := Complex.normSq (wirt (fun w => c (chartInv x w)) (chartPt x x) (stdVec 0))
  let B : ℝ := hermitianNormSq (k x) (s x) * ‖discDbarScalar c χ x‖ ^ 2 / discLeviScalar c φ x
  have hself : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel 1) x).left_inv (mem_extChartAt_source x)
  have hz : chartPt x x ∈ BundleDbar.localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (BundleDbar.localTriv (r := r) E x).baseSet
    rw [hself]
    exact mem_baseSet_trivializationAt (ComplexVector r) E x
  have hd : (gMat (flatDiscField c hc) x).det.re = d :=
    congrArg Complex.re (flatDiscField_hMat_det c hc x (mem_extChartAt_target x))
  have hpos : 0 < d := by
    rw [← hd]
    exact (Complex.pos_iff.mp (LeafProofs.gMat_posDef (flatDiscField c hc) x).det_pos).1
  have hsup : LeafProofs.inverseCurvatureCoefficientSup (r := r) E k φ
      (cutoffSourceForm E c s χ) x ≤ ENNReal.ofReal (d * B) := by
    unfold LeafProofs.inverseCurvatureCoefficientSup
    apply iSup_le
    intro U
    have he := cutoff_coefficient_quadratic_bound E c hc k φ χ hG hφ hl s x (chartPt x x) hz U
    rw [hself] at he
    exact ENNReal.ofReal_le_ofReal he
  rw [LeafProofs.inverseCurvatureNormSq_factor_of_metric E,
    LeafProofs.gMat_inv_det_re, hd]
  calc
    ENNReal.ofReal d⁻¹ * LeafProofs.inverseCurvatureCoefficientSup (r := r) E k φ
        (cutoffSourceForm E c s χ) x ≤ ENNReal.ofReal d⁻¹ * ENNReal.ofReal (d * B) :=
      mul_le_mul_right hsup _
    _ = ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
      congr 1
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

theorem cutoffInverseCurvatureBound : CutoffInverseCurvatureBound (r := r) E := by
  intro c hc g μ k φ χ hg hμ _ _ hG hφ _ hl s f _ hf
  rw [cutoffSourceForm_eq E c s χ f hf]
  rw [LeafProofs.inverseCurvatureIntegral_metric_independent E g (flatDiscField c hc) μ
    ((2 : ℝ≥0∞) • BundlePresentation.discArea c) hμ (flatDiscField_volume c hc) hg (flatDiscField_smooth c hc)]
  unfold BundleDbar.inverseCurvatureIntegral
  rw [lintegral_smul_measure, smul_eq_mul]
  apply mul_le_mul_right
  apply lintegral_mono
  intro x
  have hp := cutoff_inverse_point_bound E c hc k φ χ hG hφ hl s x
  have hB : 0 ≤ hermitianNormSq (k x) (s x) * ‖discDbarScalar c χ x‖ ^ 2 / discLeviScalar c φ x :=
    div_nonneg (mul_nonneg (hermitianNormSq_nonneg _ _) (sq_nonneg _)) (hl x).le
  exact (mul_le_mul_left hp (ENNReal.ofReal (Real.exp (-φ x)))).trans_eq
    (ENNReal.ofReal_mul hB).symm

end Yau.Proofs.B01Aux
