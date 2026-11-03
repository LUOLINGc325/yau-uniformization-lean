import Yau.LeafProofs.L14CurvatureEnergy
import Yau.LeafProofs.L14RaisedDerivatives
import Yau.LeafProofs.L14Symbols

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem star_wirtBar_ofReal {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℝ) (z v : X) :
    star (wirtBar (fun y => (f y : ℂ)) z v) = wirt (fun y => (f y : ℂ)) z v := by
  simpa only [Complex.star_def, Complex.conj_ofReal] using
    (wirt_star (fun y => (f y : ℂ)) z v).symm

def chartScalarWirt {n : ℕ} {M : ComplexManifold n} (χ : M.Carrier → ℝ)
    (a : M.Carrier) (z : ComplexVector n) : Fin n → ℂ :=
  fun i => wirt (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartScalarWirt_overlap (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (a b : M.Carrier) (z : ComplexVector n) (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    chartScalarWirt χ b z = chartScalarWirt χ a (chartPt a (chartInv b z)) ᵥ*
      (Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p) := by
  let T := fun w => chartPt a (chartInv b w)
  let fa := fun w => Complex.ofReal (inChart a χ w)
  let fb := fun w => Complex.ofReal (inChart b χ w)
  have he : fb =ᶠ[𝓝 z] (fun w => fa (T w)) := by
    filter_upwards [(bundleChartOverlap_isOpen E a b).mem_nhds hz] with w hw
    change (χ (chartInv b w) : ℂ) = (χ (chartInv a (chartPt a (chartInv b w))) : ℂ)
    rw [chartInv_chartPt_of_mem a _ (by simpa only [extChartAt_source] using hw.2.1)]
  have hfa : DifferentiableAt ℝ fa (T z) :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds
        (chartTransition_maps_bundleChartOverlap E a b hz).1)).differentiableAt (by simp)
  have hT : DifferentiableAt ℂ T z :=
    (L18Aux.chartTransition_contDiffAt b a hz.1.1 hz.2.1).differentiableAt (by simp)
  funext i
  have hd : wirtBar fb z (stdVec i) = wirtBar fa (T z) (fderiv ℂ T z (stdVec i)) := by
    have hd0 := he.fderiv_eq (𝕜 := ℝ)
    calc
      _ = wirtBar (fun w => fa (T w)) z (stdVec i) := by unfold wirtBar; rw [hd0]
      _ = _ := wirtBar_comp_complex_differentiable T fa z (stdVec i) hT hfa
  rw [wirtBar_direction_coordinates fa (T z)] at hd
  have hs := congrArg star hd
  simpa only [fa, fb, chartScalarWirt, star_wirtBar_ofReal, star_sum, star_mul,
    star_star, Matrix.vecMul, dotProduct, Matrix.of_apply, mul_comm] using hs

def chartScalarContraction (g : HermitianField M) (χ : M.Carrier → ℝ)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) : ComplexVector r :=
  WithLp.toLp 2 (chartScalarWirt χ a z ᵥ* raisedOneCoefficientsMatrix (r := r) E g u a z)

theorem chartScalarContraction_apply (g : HermitianField M) (χ : M.Carrier → ℝ)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) (α : Fin r) :
    chartScalarContraction (r := r) E g χ u a z α =
      ∑ i, ∑ j, star (wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) *
        (hMat g a z)⁻¹ i j * coefficients (r := r) E u a z (fun _ => j) α := by
  simp only [chartScalarContraction, Matrix.vecMul, dotProduct,
    raisedOneCoefficientsMatrix, Matrix.mul_apply, chartScalarWirt, oneCoefficientsMatrix,
    star_wirtBar_ofReal, Finset.mul_sum, mul_assoc]

theorem chartScalarContraction_overlap (g : HermitianField M) (χ : M.Carrier → ℝ)
    (hχ : SmoothFn χ) (u : NQForm E 1) (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    chartScalarContraction (r := r) E g χ u b z =
      topBundleTransition (r := r) E a b z
        (chartScalarContraction (r := r) E g χ u a (chartPt a (chartInv b z))) := by
  let J := Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p
  let U := raisedOneCoefficientsMatrix (r := r) E g u a (chartPt a (chartInv b z))
  let V := raisedOneCoefficientsMatrix (r := r) E g u b z
  let A := bundleFrameTransitionMatrix (r := r) E b a (chartInv b z)
  let C := bundleFrameTransitionMatrix (r := r) E a b (chartInv b z)
  have hAC : A * C = 1 := bundleFrameTransitionMatrix_mul_reverse E b a _ hz.1.2 hz.2.2
  have hJV : J * V = J.det • (U * Cᵀ) := by
    have he := congrArg (fun B : Matrix (Fin n) (Fin r) ℂ => B * Cᵀ)
      (raisedOneCoefficientsMatrix_overlap E g u a b z hz)
    change (J * V * Aᵀ) * Cᵀ = (J.det • U) * Cᵀ at he
    have ht : Aᵀ * Cᵀ = 1 := by
      rw [← Matrix.transpose_mul,
        bundleFrameTransitionMatrix_mul_reverse E a b _ hz.2.2 hz.1.2, Matrix.transpose_one]
    simpa only [Matrix.mul_assoc, ht, Matrix.mul_one, Matrix.smul_mul] using he
  have hv : chartScalarWirt χ b z ᵥ* V =
      J.det • ((chartScalarWirt χ a (chartPt a (chartInv b z)) ᵥ* U) ᵥ* Cᵀ) := by
    rw [chartScalarWirt_overlap E χ hχ a b z hz, Matrix.vecMul_vecMul, hJV,
      Matrix.vecMul_smul, ← Matrix.vecMul_vecMul]
  ext α
  have hc (v : ComplexVector r) :
      (localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) (chartInv b z) v α =
        ∑ β, C α β * v β := by
    exact complexLinear_apply_coordinates
      ((localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) (chartInv b z)) v α
  change (chartScalarWirt χ b z ᵥ* V) α = _
  rw [hv]
  change J.det * _ = J.det *
    (((localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) (chartInv b z))
      (chartScalarContraction (r := r) E g χ u a (chartPt a (chartInv b z)))) α
  rw [hc]
  simp only [Matrix.vecMul, dotProduct, Matrix.transpose_apply,
    chartScalarContraction, mul_comm]
  rfl

def scalarGradientContraction (g : HermitianField M) (χ : M.Carrier → ℝ)
    (u : NQForm E 1) : NQForm E 0 := fun x =>
  (canonicalTopTensorCoordinates (r := r) E x).symm
    (chartScalarContraction (r := r) E g χ u x (chartPt x x))

theorem coefficients_scalarGradientContraction (g : HermitianField M)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    coefficients (r := r) E (scalarGradientContraction (r := r) E g χ u) a z Fin.elim0 =
      chartScalarContraction (r := r) E g χ u a z := by
  let x := chartInv a z
  have hxa : x ∈ bundleChartSource (r := r) E a :=
    ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
  have hxx : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have ho : z ∈ bundleChartOverlap (r := r) E x a := ⟨hz, hxx⟩
  rw [← topTensorCoordinatesEquiv_form E (scalarGradientContraction (r := r) E g χ u) a z hz]
  change topTensorCoordinatesEquiv E a x hxa
    ((topTensorCoordinatesEquiv E x x hxx).symm
      (chartScalarContraction (r := r) E g χ u x (chartPt x x))) = _
  rw [topTensorCoordinatesEquiv_transition E x a x hxx hxa,
    chartFrameBasis_toMatrix_fderiv x a z hz.1 hxx.1,
    ← bundleCoordChange_apply E x a x hxx.2 hxa.2]
  exact (chartScalarContraction_overlap E g χ hχ u x a z ho).symm

theorem coefficients_scalarGradientContraction_apply (g : HermitianField M)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (α : Fin r) :
    coefficients (r := r) E (scalarGradientContraction (r := r) E g χ u) a z Fin.elim0 α =
      ∑ i, ∑ j, star (wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) *
        (hMat g a z)⁻¹ i j * coefficients (r := r) E u a z (fun _ => j) α := by
  rw [coefficients_scalarGradientContraction E g χ hχ u a z hz,
    chartScalarContraction_apply]

theorem scalar_contraction_bound {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (a : Fin n → ℂ) (F : Fin r → Fin n → ℂ) :
    (star (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α) ⬝ᵥ H *ᵥ
      (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α)).re ≤
        (star a ⬝ᵥ G⁻¹ *ᵥ a).re *
          (∑ α, ∑ β, H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β)).re := by
  have he := wedge_contraction_energy_identity_coefficients G H hG a F
  have hn := twoCoefficientNormSq_nonneg G H hG hH
    (fun α i j => a i * F α j - a j * F α i)
  linarith

set_option backward.isDefEq.respectTransparency false in
theorem chartOneCoefficientNormSq_eq_fiber_sum (g : HermitianField M) (h : Metric E)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) :
    chartOneCoefficientNormSq (r := r) E g h u a z =
      (∑ α, ∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
        (star (fun i => coefficients (r := r) E u a z (fun _ => i) α) ⬝ᵥ
          (hMat g a z)⁻¹ *ᵥ (fun j => coefficients (r := r) E u a z (fun _ => j) β))).re := by
  unfold chartOneCoefficientNormSq chartOneMetricMatrix
  rw [← metricPairing_eq_kronecker (hMat g a z)⁻¹ (BundleDbar.metricMatrix (r := r) E h a z)
    (fun i α => coefficients (r := r) E u a z (fun _ => i) α)
    (fun i α => coefficients (r := r) E u a z (fun _ => i) α)]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gradNormSq_eq_chart_bar_norm (g : HermitianField M) (χ : M.Carrier → ℝ)
    (x : M.Carrier) :
    gradNormSq g χ x =
      (star (fun i => wirtBar (fun w => Complex.ofReal (inChart x χ w)) (chartPt x x) (stdVec i)) ⬝ᵥ
        (hMat g x (chartPt x x))⁻¹ *ᵥ
          (fun i => wirtBar (fun w => Complex.ofReal (inChart x χ w)) (chartPt x x) (stdVec i))).re := by
  unfold gradNormSq dualNormMat
  simp_rw [← star_wirtBar_ofReal]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.star_apply, star_star,
    Finset.mul_sum, gMat]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem chartScalarContraction_normSq_bound (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    (star (WithLp.ofLp (chartScalarContraction (r := r) E g χ u a z)) ⬝ᵥ
      BundleDbar.metricMatrix (r := r) E h a z *ᵥ
        WithLp.ofLp (chartScalarContraction (r := r) E g χ u a z)).re ≤
      (star (fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) ⬝ᵥ
        (hMat g a z)⁻¹ *ᵥ
          (fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i))).re *
            chartOneCoefficientNormSq (r := r) E g h u a z := by
  let v := fun i => wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)
  let F := fun α i => coefficients (r := r) E u a z (fun _ => i) α
  have hc : WithLp.ofLp (chartScalarContraction (r := r) E g χ u a z) =
      fun α => star v ⬝ᵥ (hMat g a z)⁻¹ *ᵥ F α := by
    funext α
    rw [chartScalarContraction_apply]
    simp only [v, F, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [hc, chartOneCoefficientNormSq_eq_fiber_sum]
  exact scalar_contraction_bound _ _ (hMat_posDef g a z hz.1)
    (metricMatrix_posDef E h a z hz) v F

theorem scalarGradientContraction_normSq_le (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (u : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (scalarGradientContraction (r := r) E g χ u) x ≤
      gradNormSq g χ x * BundleDbar.formNormSq (r := r) E g h u x := by
  have hxx : chartInv x (chartPt x x) = x :=
    chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [hxx]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have ht := formNormSq_top_inChart E g h (scalarGradientContraction (r := r) E g χ u)
    x (chartPt x x) hz
  have hu := formNormSq_one_chart_factor E g h u x (chartPt x x) hz
  rw [hxx] at ht hu
  rw [ht, hu, coefficients_scalarGradientContraction E g χ hχ u x (chartPt x x) hz,
    gradNormSq_eq_chart_bar_norm]
  have he := mul_le_mul_of_nonneg_left
    (chartScalarContraction_normSq_bound E g h χ u x (chartPt x x) hz)
    (inv_nonneg.mpr (Complex.nonneg_iff.mp (hMat_posDef g x _ hz.1).posSemidef.det_nonneg).1)
  have hs (v : ComplexVector r) :
      (∑ α, ∑ β, star (v α) * BundleDbar.metricMatrix (r := r) E h x (chartPt x x) α β * v β) =
        star (WithLp.ofLp v) ⬝ᵥ BundleDbar.metricMatrix (r := r) E h x (chartPt x x) *ᵥ WithLp.ofLp v := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [hs]
  simpa only [mul_left_comm] using he

end Yau.LeafProofs.L14Aux
