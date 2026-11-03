import Yau.Proofs.G04LeviForms
import Yau.LeafProofs.L23RicciBound

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {M : ComplexManifold n}

/-- The value of an actual degree-zero alternating form. -/
def scalarValue (A : RealForm M 0) (x : M.Carrier) : ℝ := A x Fin.elim0

theorem scalarValue_components (A : RealForm M 0) (c : M.Carrier)
    (z : ComplexVector n) (I : Fin 0 → RIdx n) :
    formComponents A c z I = inChart c (scalarValue A) z := by
  unfold formComponents scalarValue inChart
  congr 1
  exact Subsingleton.elim _ _

theorem scalarValue_smooth (A : RealForm M 0) (hA : SmoothRealForm A) :
    SmoothFn (scalarValue A) := by
  intro c
  simpa only [scalarValue_components] using hA c Fin.elim0

theorem scalarValue_compact (A : RealForm M 0) (hcA : CompactlySupportedRealForm A) :
    HasCompactSupport (scalarValue A) := by
  apply hcA.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx hzero
  apply hx
  simp [scalarValue, hzero]

theorem formInner_scalar (g : HermitianField M) (f : M.Carrier → ℝ)
    (A : RealForm M 0) (x : M.Carrier) :
    formInner g (scalarForm f) A x = f x * scalarValue A x := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  simp only [formInner, scalarValue_components]
  simp only [inChart, hx]
  simp [scalarValue, scalarForm]

theorem formInner_one (g : HermitianField M) (A B : RealForm M 1) (x : M.Carrier) :
    formInner g A B x = ∑ a, ∑ b,
      formComponents A x (chartPt x x) (fun _ => a) *
      formComponents B x (chartPt x x) (fun _ => b) *
      (realMetricFn g x (chartPt x x))⁻¹ a b := by
  simp only [formInner, L23Aux.sum_tensor_cons, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.cons_zero, Fintype.sum_unique, Nat.factorial_one, Nat.cast_one, inv_one,
    one_mul, mul_one]
  have hcons (a : RIdx n) : Fin.cons a (default : Fin 0 → RIdx n) = fun _ : Fin 1 => a := by
    funext i
    fin_cases i
    rfl
  simp only [hcons]

theorem jPullbackOne_square (A : RealForm M 1) :
    jPullbackForm (jPullbackForm A) = (-1 : ℝ) • A := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro V
  change A x (fun i => Complex.I • (Complex.I • V i)) = (-1 : ℝ) * A x V
  have hv : (fun i : Fin 1 => Complex.I • (Complex.I • V i)) = fun i => (-1 : ℝ) • V i := by
    funext i
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hv, ContinuousAlternatingMap.map_smul_univ]
  simp

/-- The actual pullback by J is an isometry on real covectors. -/
theorem formInner_jPullbackOne (g : HermitianField M) (A B : RealForm M 1)
    (x : M.Carrier) :
    formInner g (jPullbackForm A) (jPullbackForm B) x = formInner g A B x := by
  rw [formInner_one, formInner_one]
  simp only [jPullbackForm_components]
  rw [← L18Aux.sum_jIndex_two (fun a b =>
    formComponents A x (chartPt x x) (fun _ => a) *
      formComponents B x (chartPt x x) (fun _ => b) *
      (realMetricFn g x (chartPt x x))⁻¹ a b)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hi : (realMetricFn g x (chartPt x x))⁻¹ (L18Aux.jIndex n a) (L18Aux.jIndex n b) =
      L18Aux.jSign a * L18Aux.jSign b * (realMetricFn g x (chartPt x x))⁻¹ a b := by
    simpa only [chartPt] using
      (L18Aux.realMetricFn_inverse_jIndex g x (mem_extChartAt_target x) a b)
  rw [hi]
  change (L12Aux.jSign a * _) * (L12Aux.jSign b * _) * _ =
    _ * _ * (L12Aux.jSign a * L12Aux.jSign b * _)
  simp only [L18Aux.jIndex, L12Aux.jIndex]
  ring

/-- Degree one has J* = -J; this determines the dd-adjoint sign. -/
theorem formInner_jPullbackOne_skew (g : HermitianField M) (A B : RealForm M 1)
    (x : M.Carrier) :
    formInner g (jPullbackForm A) B x = -formInner g A (jPullbackForm B) x := by
  have he := formInner_jPullbackOne g A (jPullbackForm B) x
  rw [jPullbackOne_square, formInner_smul_right] at he
  change (-1 : ℝ) * formInner g (jPullbackForm A) B x = _ at he
  linarith

theorem jPullbackOne_smooth (A : RealForm M 1) (hA : SmoothRealForm A) :
    SmoothRealForm (jPullbackForm A) := by
  intro c I
  apply (contDiffOn_const.mul (hA c (fun _ => L12Aux.jIndex n (I 0)))).congr
  intro z _
  exact jPullbackForm_components A c z I

theorem jPullbackOne_support (A : RealForm M 1) :
    closure {x | jPullbackForm A x ≠ 0} ⊆ closure {x | A x ≠ 0} := by
  apply closure_mono
  intro x hx hz
  apply hx
  apply ContinuousAlternatingMap.ext
  intro V
  simp [jPullbackForm, hz]

theorem jPullbackOne_compact (A : RealForm M 1) (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (jPullbackForm A) :=
  hcA.of_isClosed_subset isClosed_closure (jPullbackOne_support A)

/-- The scalar formal adjoint of dd = -(1/2)dJ*d, in the actual metric. -/
def ddAdjointScalar (g : HermitianField M) (B : RealForm M 2) : M.Carrier → ℝ :=
  fun x => (1 / 2 : ℝ) * scalarValue
    (codifferentialRealForm g (jPullbackForm (codifferentialRealForm g B))) x

theorem ddAdjointScalar_smooth (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2) (hB : SmoothRealForm B) :
    SmoothFn (ddAdjointScalar g.form B) := by
  have hδB := codifferentialRealForm_smooth g μ hμ B hB
  have hJ := jPullbackOne_smooth _ hδB
  have hδJ := codifferentialRealForm_smooth g μ hμ _ hJ
  intro c
  exact contDiffOn_const.mul (scalarValue_smooth _ hδJ c)

theorem ddAdjointScalar_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    HasCompactSupport (ddAdjointScalar g.form B) := by
  have hδB := codifferentialRealForm_smooth g μ hμ B hB
  have hcδB := codifferentialRealForm_compactlySupported g μ hμ B hB hcB
  have hJ := jPullbackOne_smooth _ hδB
  have hcJ := jPullbackOne_compact _ hcδB
  exact (scalarValue_compact _ (codifferentialRealForm_compactlySupported g μ hμ _ hJ hcJ)).mul_left

end Yau.NodeProofs.P06Aux.WeakCurrent
