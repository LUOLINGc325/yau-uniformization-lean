import Yau.LeafProofs.L21FlatEnergy
import Yau.LeafProofs.L21CompactTests

/-! The compact first-order estimate uses only the size of the principal
matrix. Its constant does not depend on derivatives of the coefficients. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def holVector (f : X n → ℂ) (x : X n) : X n :=
  WithLp.toLp 2 (fun i => Yau.wirt f x (Yau.stdVec i))

def barVector (f : X n → ℂ) (x : X n) : X n :=
  WithLp.toLp 2 (fun i => Yau.wirtBar f x (Yau.stdVec i))

def graphDerivative (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (f : X n → ℂ) (x : X n) : X n :=
  WithLp.toLp 2 (fun i => dbarA A i f x)

theorem graphDerivative_eq (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (f : X n → ℂ) (x : X n) :
    graphDerivative A f x = barVector f x +
      (Matrix.toEuclideanLin (A x)).toContinuousLinearMap (holVector f x) := by
  ext i
  rfl

theorem barVector_norm_sq_le
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (f : X n → ℂ) (x : X n)
    (hA : Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) :
    ‖barVector f x‖ ^ 2 ≤ 2 * ‖graphDerivative A f x‖ ^ 2 +
      (1 / 2 : ℝ) * ‖holVector f x‖ ^ 2 := by
  have hM : ‖(Matrix.toEuclideanLin (A x)).toContinuousLinearMap (holVector f x)‖ ≤
      (1 / 2 : ℝ) * ‖holVector f x‖ :=
    ((Matrix.toEuclideanLin (A x)).toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have he : barVector f x = graphDerivative A f x -
      (Matrix.toEuclideanLin (A x)).toContinuousLinearMap (holVector f x) := by
    rw [graphDerivative_eq, add_sub_cancel_right]
  have hb := (norm_sub_le (graphDerivative A f x)
    ((Matrix.toEuclideanLin (A x)).toContinuousLinearMap (holVector f x))).trans
      (add_le_add (le_refl _) hM)
  rw [← he] at hb
  have hsq := sq_le_sq₀ (norm_nonneg (barVector f x))
    (by positivity : 0 ≤ ‖graphDerivative A f x‖ + (1 / 2 : ℝ) * ‖holVector f x‖)
  have hs := hsq.mpr hb
  nlinarith [sq_nonneg (‖graphDerivative A f x‖ - (1 / 2 : ℝ) * ‖holVector f x‖)]

theorem contDiff_wirt {f : X n → ℂ} (hf : ContDiff ℝ ∞ f) (v : X n) :
    ContDiff ℝ ∞ (fun x => Yau.wirt f x v) := by
  unfold Yau.wirt
  exact contDiff_const.mul ((contDiff_directional hf v).sub
    (contDiff_const.mul (contDiff_directional hf (Complex.I • v))))

theorem contDiff_wirtBar {f : X n → ℂ} (hf : ContDiff ℝ ∞ f) (v : X n) :
    ContDiff ℝ ∞ (fun x => Yau.wirtBar f x v) := by
  unfold Yau.wirtBar
  exact contDiff_const.mul ((contDiff_directional hf v).add
    (contDiff_const.mul (contDiff_directional hf (Complex.I • v))))

theorem tsupport_wirt_subset (f : X n → ℂ) (v : X n) :
    tsupport (fun x => Yau.wirt f x v) ⊆ tsupport f := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  exact hx (by simp [Yau.wirt, fderiv_of_notMem_tsupport ℝ hn])

theorem tsupport_wirtBar_subset (f : X n → ℂ) (v : X n) :
    tsupport (fun x => Yau.wirtBar f x v) ⊆ tsupport f := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  exact hx (by simp [Yau.wirtBar, fderiv_of_notMem_tsupport ℝ hn])

theorem integrable_wirt_norm_sq {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (v : X n) :
    Integrable (fun x => ‖Yau.wirt f x v‖ ^ 2) (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  exact ((contDiff_wirt hf v).continuous.memLp_of_hasCompactSupport
    (hcf.mono' ((subset_tsupport _).trans (tsupport_wirt_subset f v)))).integrable_norm_pow
      (p := 2) (by decide)

theorem integrable_wirtBar_norm_sq {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (v : X n) :
    Integrable (fun x => ‖Yau.wirtBar f x v‖ ^ 2) (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  exact ((contDiff_wirtBar hf v).continuous.memLp_of_hasCompactSupport
    (hcf.mono' ((subset_tsupport _).trans (tsupport_wirtBar_subset f v)))).integrable_norm_pow
      (p := 2) (by decide)

theorem integrable_dbarA_norm_sq {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : CompactTest O) (i : Fin n) :
    Integrable (fun x => ‖dbarA A i f x‖ ^ 2) (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let g := testD hO hA i f
  exact (g.property.1.continuous.memLp_of_hasCompactSupport g.property.2.1).integrable_norm_pow
    (p := 2) (by decide)

theorem first_order_energy_on_compact_tests {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (f : CompactTest O) :
    (∑ a : Yau.RIdx n, ∫ x, ‖fderiv ℝ f x (Yau.realVec a)‖ ^ 2 ∂Yau.lebesgueC n) ≤
      16 * ∑ i : Fin n, ∫ x, ‖dbarA A i f x‖ ^ 2 ∂Yau.lebesgueC n := by
  have hb : Integrable (fun x => ‖barVector f x‖ ^ 2) (Yau.lebesgueC n) := by
    simp only [EuclideanSpace.norm_sq_eq, barVector, PiLp.toLp_apply]
    exact integrable_finsetSum _ (fun i _ => integrable_wirtBar_norm_sq f.property.1 f.property.2.1 _)
  have hh : Integrable (fun x => ‖holVector f x‖ ^ 2) (Yau.lebesgueC n) := by
    simp only [EuclideanSpace.norm_sq_eq, holVector, PiLp.toLp_apply]
    exact integrable_finsetSum _ (fun i _ => integrable_wirt_norm_sq f.property.1 f.property.2.1 _)
  have hd : Integrable (fun x => ‖graphDerivative A f x‖ ^ 2) (Yau.lebesgueC n) := by
    simp only [EuclideanSpace.norm_sq_eq, graphDerivative, PiLp.toLp_apply]
    exact integrable_finsetSum _ (fun i _ => integrable_dbarA_norm_sq hO hA f i)
  have hp (x : X n) : ‖barVector f x‖ ^ 2 ≤
      2 * ‖graphDerivative A f x‖ ^ 2 + (1 / 2 : ℝ) * ‖holVector f x‖ ^ 2 := by
    by_cases hx : x ∈ O
    · exact barVector_norm_sq_le A f x (hsmall x hx)
    · have hdx := fderiv_of_notMem_tsupport ℝ (fun hh => hx (f.property.2.2 hh))
      have hzero : barVector f x = 0 := by ext i; simp [barVector, Yau.wirtBar, hdx]
      rw [hzero, norm_zero, zero_pow (by decide)]
      positivity
  have hir : Integrable (fun x => 2 * ‖graphDerivative A f x‖ ^ 2 +
      (1 / 2 : ℝ) * ‖holVector f x‖ ^ 2) (Yau.lebesgueC n) :=
    (hd.const_mul 2).add (hh.const_mul (1 / 2 : ℝ))
  have hi := integral_mono hb hir hp
  rw [integral_add (hd.const_mul 2) (hh.const_mul (1 / 2 : ℝ)), integral_const_mul,
    integral_const_mul] at hi
  simp only [EuclideanSpace.norm_sq_eq, barVector, holVector, graphDerivative, PiLp.toLp_apply] at hi
  rw [integral_finsetSum _ (fun i _ => integrable_wirtBar_norm_sq f.property.1 f.property.2.1 _),
    integral_finsetSum _ (fun i _ => integrable_dbarA_norm_sq hO hA f i),
    integral_finsetSum _ (fun i _ => integrable_wirt_norm_sq f.property.1 f.property.2.1 _)] at hi
  have hbar := real_gradient_energy_eq_four_bar f.property.1 f.property.2.1
  have hhol := real_gradient_energy_eq_four_hol f.property.1 f.property.2.1
  linarith

end Yau.LeafProofs.L21Aux
