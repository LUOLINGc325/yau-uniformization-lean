import Yau.Proofs.P06WeitzenbockTypeMetric
import Yau.Proofs.P06WeitzenbockEndomorphism

noncomputable section
open Filter
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def matrixCovariantDerivative (h : HermitianField M) (c : M.Carrier)
    (K : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ) (z : ComplexVector n) (a : RIdx n) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  matrixDirectionalDerivative K z (realVec a) - (connectionMatrix h c z a)ᵀ * K z -
    K z * connectionMatrix h c z a

theorem matrixCovariantDerivative_form (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) (a : RIdx n) :
    matrixCovariantDerivative h c (chartFormMatrix A c) z a = covariantTwoMatrix h A c z a := by
  rw [matrixCovariantDerivative, chartFormMatrix_derivative]
  abel

theorem matrixCovariantDerivative_congr (h : HermitianField M) (c : M.Carrier)
    (K L : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ) (z : ComplexVector n)
    (he : K =ᶠ[𝓝 z] L) (a : RIdx n) :
    matrixCovariantDerivative h c K z a = matrixCovariantDerivative h c L z a := by
  unfold matrixCovariantDerivative
  rw [matrixDirectionalDerivative_congr he, he.self_of_nhds]

theorem matrixCovariantDerivative_J (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (c : M.Carrier)
    (K : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hK : ∀ i j, DifferentiableAt ℝ (fun w => K w i j) z) (a : RIdx n) :
    matrixCovariantDerivative h c (fun w => (jMatrix n)ᵀ * K w * jMatrix n) z a =
      (jMatrix n)ᵀ * matrixCovariantDerivative h c K z a * jMatrix n := by
  let J := jMatrix n
  let G := connectionMatrix h c z a
  have hJ (i j : RIdx n) : DifferentiableAt ℝ (fun _ : ComplexVector n => J i j) z :=
    differentiableAt_const _
  have hJT (i j : RIdx n) : DifferentiableAt ℝ (fun _ : ComplexVector n => Jᵀ i j) z :=
    differentiableAt_const _
  have hzero : matrixDirectionalDerivative (fun _ : ComplexVector n => J) z (realVec a) = 0 := by
    ext i j
    simp [matrixDirectionalDerivative]
  have hzeroT : matrixDirectionalDerivative (fun _ : ComplexVector n => Jᵀ) z (realVec a) = 0 := by
    ext i j
    simp [matrixDirectionalDerivative]
  have hc : G * J = J * G := (G01Aux.connectionMatrix_commute_jMatrix h hs hk c z hz a).eq
  have hct : Gᵀ * Jᵀ = Jᵀ * Gᵀ := by
    have he := congrArg Matrix.transpose hc
    simpa only [Matrix.transpose_mul] using he.symm
  have h₁ : Gᵀ * (Jᵀ * K z * J) = Jᵀ * (Gᵀ * K z) * J := by
    calc
      _ = (Gᵀ * Jᵀ) * K z * J := by noncomm_ring
      _ = _ := by rw [hct]; noncomm_ring
  have h₂ : (Jᵀ * K z * J) * G = Jᵀ * (K z * G) * J := by
    calc
      _ = Jᵀ * K z * (J * G) := by noncomm_ring
      _ = _ := by rw [← hc]; noncomm_ring
  unfold matrixCovariantDerivative
  rw [matrixDirectionalDerivative_mul (matrix_entries_differentiable_mul hJT hK) hJ,
    matrixDirectionalDerivative_mul hJT hK, hzero, hzeroT]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  change Jᵀ * matrixDirectionalDerivative K z (realVec a) * J -
    Gᵀ * (Jᵀ * K z * J) - (Jᵀ * K z * J) * G = _
  rw [h₁, h₂]
  noncomm_ring

theorem covariantTwoMatrix_jPullback (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a : RIdx n) :
    covariantTwoMatrix h (jPullbackRealForm A) c z a =
      (jMatrix n)ᵀ * covariantTwoMatrix h A c z a * jMatrix n := by
  have hK : chartFormMatrix (jPullbackRealForm A) c =
      fun w => (jMatrix n)ᵀ * chartFormMatrix A c w * jMatrix n :=
    funext (chartFormMatrix_jPullback A c)
  rw [← matrixCovariantDerivative_form, hK,
    matrixCovariantDerivative_J h hs hk c _ hz]
  · rw [matrixCovariantDerivative_form]
  · intro i j
    exact ((hA c ![i,j]).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)

def secondTwoMatrix (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (a b : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun d e => secondTwo h A c z a b d e

theorem secondTwoMatrix_formula (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    secondTwoMatrix h A c z a b =
      matrixCovariantDerivative h c (fun w => covariantTwoMatrix h A c w b) z a -
        ∑ p, christoffel h c z p a b • covariantTwoMatrix h A c z p := by
  ext d e
  simp only [secondTwoMatrix, secondTwo_formula, matrixCovariantDerivative,
    matrixDirectionalDerivative, covariantTwoMatrix, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, rDeriv]
  simp only [mul_comm]
  ring

theorem secondTwoMatrix_jPullback (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b : RIdx n) :
    secondTwoMatrix h (jPullbackRealForm A) c z a b =
      (jMatrix n)ᵀ * secondTwoMatrix h A c z a b * jMatrix n := by
  have hloc : (fun w => covariantTwoMatrix h (jPullbackRealForm A) c w b) =ᶠ[𝓝 z]
      (fun w => (jMatrix n)ᵀ * covariantTwoMatrix h A c w b * jMatrix n) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    exact covariantTwoMatrix_jPullback h hs hk A hA c hw b
  have hU (d e : RIdx n) :
      DifferentiableAt ℝ (fun w => covariantTwoMatrix h A c w b d e) z := by
    exact ((covariantComponents_smooth h hs c (formComponents A c) (hA c) b ![d,e]).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have he : matrixCovariantDerivative h c
      (fun w => covariantTwoMatrix h (jPullbackRealForm A) c w b) z a =
      (jMatrix n)ᵀ * matrixCovariantDerivative h c
        (fun w => covariantTwoMatrix h A c w b) z a * jMatrix n := by
    rw [matrixCovariantDerivative_congr h c _ _ z hloc a,
      matrixCovariantDerivative_J h hs hk c _ hz hU a]
  rw [secondTwoMatrix_formula, secondTwoMatrix_formula, he]
  simp_rw [covariantTwoMatrix_jPullback h hs hk A hA c hz]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

def roughTwoMatrix (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun d e => roughTwoComponents h A c z ![d,e]

theorem roughTwoMatrix_formula (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) :
    roughTwoMatrix h A c z = -(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b • secondTwoMatrix h A c z a b) := by
  ext d e
  simp only [roughTwoMatrix, roughTwoComponents, secondTwoMatrix, secondTwo,
    Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem roughTwoMatrix_jPullback (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    roughTwoMatrix h (jPullbackRealForm A) c z =
      (jMatrix n)ᵀ * roughTwoMatrix h A c z * jMatrix n := by
  rw [roughTwoMatrix_formula, roughTwoMatrix_formula]
  simp_rw [secondTwoMatrix_jPullback h hs hk A hA c hz]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

end Yau.NodeProofs.P06Weitzenbock
