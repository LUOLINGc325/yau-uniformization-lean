import Yau.Proofs.P06WeitzenbockCurvature

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G01Aux L23Aux G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- The inverse-metric insertion required by the conjugate-first convention. -/
def raisedFormMatrix (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    Matrix (Fin n) (Fin n) ℂ :=
  (gMat h x)⁻¹ * formHermitianMatrix A x * (gMat h x)⁻¹

def chernActionMatrix (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    Matrix (Fin n) (Fin n) ℂ := fun a b =>
  ∑ k, ∑ l, chernCurvature h x b a k l * raisedFormMatrix h A x k l

theorem chern_relative_trace (h : HermitianField M) (hs : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (A : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) :
    Matrix.trace (chernF h c z k l * (hMat h c z)⁻¹ * A) =
      ∑ i, ∑ j, chernInChart h c z i j k l *
        ((hMat h c z)⁻¹ * A * (hMat h c z)⁻¹) i j := by
  let H := hMat h c z
  let B := H⁻¹ * A * H⁻¹
  have hInv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H
    ((L12Aux.hMat_posDef h c z hz).isUnit.map Matrix.detMonoidHom)
  have he : Matrix.trace (chernF h c z k l * H⁻¹ * A) =
      Matrix.trace (H * chernF h c z k l * B) := by
    conv_rhs => rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    simp only [B, Matrix.mul_assoc, hInv, Matrix.mul_one]
  rw [he]
  change (∑ j, ∑ i, (H * chernF h c z k l) j i * B i j) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (H * chernF h c z k l) j i * B i j = _
  rw [chernF_lower h hs c z hz i j k l]

theorem raisedFormMatrix_isHermitian (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (x : M.Carrier) : (raisedFormMatrix h A x).IsHermitian := by
  have hH : ((gMat h x)⁻¹).IsHermitian :=
    (L12Aux.hMat_isHermitian h x (chartPt x x)).inv
  have hA : (formHermitianMatrix A x).IsHermitian := (representsSelf A h11).2 x
  change ((gMat h x)⁻¹ * formHermitianMatrix A x * (gMat h x)⁻¹)ᴴ =
    (gMat h x)⁻¹ * formHermitianMatrix A x * (gMat h x)⁻¹
  simp only [Matrix.conjTranspose_mul, hH.eq, hA.eq, Matrix.mul_assoc]

/-- Finite complex contraction: this hypothesis is just the tensor's
conjugation symmetry, independent of any differential operator identity. -/
theorem curvature_contraction_star
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, star (R i j k l) = R j i l k)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) (k l : Fin n) :
    star (∑ i, ∑ j, R i j k l * B i j) =
      ∑ i, ∑ j, R i j l k * B i j := by
  simp only [star_sum, star_mul, hR]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB.apply i j]
  ring

def mixedTraceMatrix (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun d e => 2 * (realDirectionFactor d * star (realDirectionFactor e) * T d.1 e.1 -
    realDirectionFactor e * star (realDirectionFactor d) * T e.1 d.1).im

/-- The real mixed-direction contraction represents minus twice the complex
contraction. The transpose is forced by the conjugate-first convention. -/
theorem mixedTraceMatrix_eq_raw (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian) :
    mixedTraceMatrix T = (4 : ℝ) • (rawReal Tᵀ * L12Aux.jMatrix n) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  have hre := congrArg Complex.re (hT.apply i j)
  have him := congrArg Complex.im (hT.apply i j)
  rw [Matrix.smul_apply, smul_eq_mul, L12Aux.mul_jMatrix]
  fin_cases a <;> fin_cases b <;>
    simp [mixedTraceMatrix, realDirectionFactor, rawReal, Matrix.transpose_apply,
      L12Aux.jIndex, L12Aux.jSign, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im] at hre him ⊢ <;> linarith

def chernTraceMatrix (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    Matrix (Fin n) (Fin n) ℂ := fun k l =>
  Matrix.trace (chernF h x (chartPt x x) k l * (gMat h x)⁻¹ * formHermitianMatrix A x)

theorem chernTraceMatrix_isHermitian_of_star (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier)
    (hstar : ∀ i j k l, star (chernCurvature h x i j k l) =
      chernCurvature h x j i l k) : (chernTraceMatrix h A x).IsHermitian := by
  ext k l
  simp only [Matrix.conjTranspose_apply, chernTraceMatrix]
  simp only [gMat]
  rw [chern_relative_trace h hs x (z := chartPt x x) (mem_extChartAt_target x),
    chern_relative_trace h hs x (z := chartPt x x) (mem_extChartAt_target x)]
  exact curvature_contraction_star (chernCurvature h x) hstar
    (raisedFormMatrix h A x) (raisedFormMatrix_isHermitian h A h11 x) l k

theorem chernTraceMatrix_transpose_of_pair (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (x : M.Carrier)
    (hpair : ∀ i j k l, chernCurvature h x i j k l = chernCurvature h x k l i j) :
    (chernTraceMatrix h A x)ᵀ = chernActionMatrix h A x := by
  ext a b
  simp only [Matrix.transpose_apply, chernTraceMatrix, gMat]
  rw [chern_relative_trace h hs x (z := chartPt x x) (mem_extChartAt_target x)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change chernCurvature h x k l b a * raisedFormMatrix h A x k l = _
  rw [hpair]

def crossCurvatureMatrix (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    Matrix (RIdx n) (RIdx n) ℝ := fun d e =>
  Matrix.trace (L12Aux.curvatureMatrix h x (chartPt x x) d e *
    (realMetricFn h x (chartPt x x))⁻¹ * realFormMatrix A x)

theorem crossCurvatureMatrix_eq_mixedTrace (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier) :
    crossCurvatureMatrix h A x = mixedTraceMatrix (chernTraceMatrix h A x) := by
  ext d e
  rw [crossCurvatureMatrix, curvature_cross_trace_complex h hs hk A h11,
    complexCurvatureRealDirections_eq h hs x (chartPt x x) (mem_extChartAt_target x) d e]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, mixedTraceMatrix, chernTraceMatrix]

theorem crossCurvatureMatrix_eq_chernAction_of_symmetries
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier)
    (hstar : ∀ i j k l, star (chernCurvature h x i j k l) = chernCurvature h x j i l k)
    (hpair : ∀ i j k l, chernCurvature h x i j k l = chernCurvature h x k l i j) :
    crossCurvatureMatrix h A x =
      (4 : ℝ) • (rawReal (chernActionMatrix h A x) * L12Aux.jMatrix n) := by
  rw [crossCurvatureMatrix_eq_mixedTrace h hs hk A h11 x,
    mixedTraceMatrix_eq_raw _ (chernTraceMatrix_isHermitian_of_star h hs A h11 x hstar),
    chernTraceMatrix_transpose_of_pair h hs A x hpair]

theorem raw_ricci_action (R H A : Matrix (Fin n) (Fin n) ℂ) :
    ((2 : ℝ) • rawReal R) * ((1 / 2 : ℝ) • rawReal H) *
        ((-2 : ℝ) • (rawReal A * L12Aux.jMatrix n)) +
      ((-2 : ℝ) • (rawReal A * L12Aux.jMatrix n)) *
        ((1 / 2 : ℝ) • rawReal H) * ((2 : ℝ) • rawReal R) =
      (-2 : ℝ) • (rawReal (R * H * A + A * H * R) * L12Aux.jMatrix n) := by
  have he : rawReal A * L12Aux.jMatrix n * rawReal H * rawReal R =
      rawReal A * rawReal H * rawReal R * L12Aux.jMatrix n := by
    calc
      _ = rawReal A * (L12Aux.jMatrix n * rawReal H) * rawReal R := by noncomm_ring
      _ = rawReal A * (rawReal H * L12Aux.jMatrix n) * rawReal R := by
        rw [rawReal_commute_J]
      _ = rawReal A * rawReal H * (L12Aux.jMatrix n * rawReal R) := by noncomm_ring
      _ = _ := by rw [rawReal_commute_J]; noncomm_ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    rawReal_add, rawReal_mul, Matrix.add_mul, Matrix.mul_add]
  norm_num only [show (2 : ℝ) * (1 / 2) * (-2) = -2 by norm_num,
    show (-2 : ℝ) * (1 / 2) * 2 = -2 by norm_num]
  rw [he]
  simp only [Matrix.mul_assoc, smul_add]

/-- Full relative Hermitian curvature action, valid for signed input. -/
def hermitianCurvatureReaction (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    Matrix (Fin n) (Fin n) ℂ :=
  ricci h x * (gMat h x)⁻¹ * formHermitianMatrix A x +
    formHermitianMatrix A x * (gMat h x)⁻¹ * ricci h x -
      (2 : ℂ) • chernActionMatrix h A x

theorem curvatureTwoMatrix_eq_raw_reaction_of_symmetries
    (g : SmoothMetric M) (hk : IsKahler g) (A : RealForm M 2) (h11 : RealOneOne A)
    (x : M.Carrier)
    (hstar : ∀ i j k l, star (chernCurvature g.form x i j k l) =
      chernCurvature g.form x j i l k)
    (hpair : ∀ i j k l, chernCurvature g.form x i j k l =
      chernCurvature g.form x k l i j) :
    (fun d e => curvatureTwoComponents g.form A x (chartPt x x) ![d,e]) =
      (-2 : ℝ) • (rawReal (hermitianCurvatureReaction g.form A x) * L12Aux.jMatrix n) := by
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  have hK : chartFormMatrix A x (chartPt x x) = realFormMatrix A x := by
    ext d e
    exact formComponents_center_pair A x ![d,e]
  have hR : L12Aux.realRicciMatrix g.form x (chartPt x x) =
      (2 : ℝ) • rawReal (ricci g.form x) := by
    rw [L12Aux.realRicciMatrix_eq_realification g hk x (chartPt x x)
      (mem_extChartAt_target x), hermitianRealification_eq]
    rfl
  have he : (fun d e => curvatureTwoComponents g.form A x (chartPt x x) ![d,e]) =
      L12Aux.realRicciMatrix g.form x (chartPt x x) *
          (realMetricFn g.form x (chartPt x x))⁻¹ * realFormMatrix A x +
        realFormMatrix A x * (realMetricFn g.form x (chartPt x x))⁻¹ *
          L12Aux.realRicciMatrix g.form x (chartPt x x) + crossCurvatureMatrix g.form A x := by
    ext d e
    simpa only [hK, Matrix.add_apply, crossCurvatureMatrix] using
      (curvatureTwo_eq_ricci_matrix g.form hs A x (z := chartPt x x)
        (mem_extChartAt_target x) d e)
  rw [he, hR, G01Aux.realMetricFn_inverse_eq g.form x (chartPt x x)
    (mem_extChartAt_target x), realFormMatrix_eq_raw A h11 x,
    raw_ricci_action, crossCurvatureMatrix_eq_chernAction_of_symmetries
      g.form hs hk A h11 x hstar hpair]
  have hraw2 : rawReal ((2 : ℂ) • chernActionMatrix g.form A x) =
      (2 : ℝ) • rawReal (chernActionMatrix g.form A x) :=
    rawReal_real_smul (2 : ℝ) _
  simp only [hermitianCurvatureReaction, rawReal_sub, hraw2, gMat,
    Matrix.sub_mul, Matrix.smul_mul, smul_sub, smul_smul]
  norm_num only [show (-2 : ℝ) * 2 = -4 by norm_num, neg_smul,
    sub_neg_eq_add]

/-- In an h-unitary frame the paper's normalized HBC is exactly the real
Chern coefficient; the numerator's factor four cancels its denominator. -/
theorem hbc_unit_norm_eq_chern (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (u v : TangentVector M x)
    (hu : hermitianNormSq (h x) u = 1) (hv : hermitianNormSq (h x) v = 1) :
    paperHolomorphicBisectionalCurvature h x u v =
      bisectionalForm h x (tangentCoordinates x u) (tangentCoordinates x v) := by
  unfold paperHolomorphicBisectionalCurvature
  rw [paper_numerator_eq_bisectionalForm h hs hk, hu, hv]
  ring

end Yau.NodeProofs.P06Weitzenbock
