import Yau.LeafProofs.L05AutonomousLocalFrame
import Yau.LeafProofs.L05AutonomousPeanoMeasurableLimit
import Yau.LeafProofs.L05AutonomousPeanoMeasurableSecond

noncomputable section
open Filter Set MeasureTheory Asymptotics Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Canonical directional values use actual finite centered differences. -/
def peanoDirectionalLimit {n : ℕ} (u : Point n → ℝ) (e : Space n) (p : Point n) : ℝ :=
  peanoRealSequenceLimit (fun j => autoSecond u e (peanoDyadicStep j) p)

def peanoMeasurableMatrix {n : ℕ} (u : Point n → ℝ) (p : Point n) : Mat n :=
  fun i j => if i=j then peanoDirectionalLimit u (Yau.realVec i) p else
    peanoDirectionalLimit u (autoPairDirection i j) p-
      (peanoDirectionalLimit u (Yau.realVec i) p+
        peanoDirectionalLimit u (Yau.realVec j) p)/2

/-- The canonical measurable candidate depends only on u, and uses the native
symmetric projection in the actual Frobenius matrix space. -/
def peanoMeasurableHessian {n : ℕ} (u : Point n → ℝ) (p : Point n) : Sym n :=
  sym (peanoMeasurableMatrix u p)

theorem measurable_peanoDirectionalLimit {n : ℕ} {u : Point n → ℝ}
    (hu : Continuous u) (e : Space n) : Measurable (peanoDirectionalLimit u e) := by
  apply measurable_peanoRealSequenceLimit
  intro j
  have hc : Continuous (fun p : Point n => autoSecond u e (peanoDyadicStep j) p) := by
    unfold autoSecond
    fun_prop
  exact hc.measurable

theorem measurable_peanoMeasurableMatrix {n : ℕ} {u : Point n → ℝ}
    (hu : Continuous u) : Measurable (peanoMeasurableMatrix u) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  by_cases hij : i=j
  · simpa only [peanoMeasurableMatrix,ite_eq_left hij] using
      measurable_peanoDirectionalLimit hu (Yau.realVec i)
  · simp only [peanoMeasurableMatrix,ite_eq_right hij]
    have hMeas := (measurable_peanoDirectionalLimit hu (autoPairDirection i j)).sub
        (((measurable_peanoDirectionalLimit hu (Yau.realVec i)).add
          (measurable_peanoDirectionalLimit hu (Yau.realVec j))).div_const 2)
    convert! hMeas using 1 <;> ext p <;> rfl

theorem measurable_peanoMeasurableHessian {n : ℕ} {u : Point n → ℝ}
    (hu : Continuous u) : Measurable (peanoMeasurableHessian u) :=
  (continuous_selfAdjointPart ℝ (Mat n)).measurable.comp (measurable_peanoMeasurableMatrix hu)

theorem peanoMeasurableMatrix_symmetric {n : ℕ} (u : Point n → ℝ) (p : Point n)
    (i j : Yau.RIdx n) : peanoMeasurableMatrix u p i j=peanoMeasurableMatrix u p j i := by
  classical
  by_cases hij : i=j
  · subst j
    rfl
  have hPair : autoPairDirection i j=autoPairDirection j i := by
    simp only [autoPairDirection,add_comm]
  simp only [peanoMeasurableMatrix,ite_eq_right hij,ite_eq_right (Ne.symm hij),hPair,add_comm]

theorem peanoMeasurableHessian_coe {n : ℕ} (u : Point n → ℝ) (p : Point n) :
    (peanoMeasurableHessian u p : Mat n)=peanoMeasurableMatrix u p := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  apply Matrix.isHermitian_iff_isSelfAdjoint.mp
  apply Matrix.IsHermitian.ext
  intro i j
  simpa only [star_trivial] using peanoMeasurableMatrix_symmetric u p j i

theorem peano_bilinear_pair {n : ℕ}
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (i j : Yau.RIdx n) :
    B (autoPairDirection i j) (autoPairDirection i j)=
      (B (Yau.realVec i) (Yau.realVec i)+B (Yau.realVec j) (Yau.realVec j))/2+
        B (Yau.realVec i) (Yau.realVec j) := by
  simp only [autoPairDirection,map_smul,map_add,_root_.smul_apply,
    _root_.add_apply,smul_eq_mul]
  rw [hB (Yau.realVec j) (Yau.realVec i)]
  have hsqrt : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hne]
  rw [hsqrt]
  ring

theorem peanoMeasurableHessian_entries_of_peano {n : ℕ} {u : Point n → ℝ} {p : Point n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hB : ∀ v w, B v w=B w v)
    (hRem : (fun y => u (y,p.2)-u p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))
      =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) (i j : Yau.RIdx n) :
    (peanoMeasurableHessian u p : Mat n) i j=B (Yau.realVec i) (Yau.realVec j) := by
  classical
  have hLimit (e : Space n) : peanoDirectionalLimit u e p=B e e :=
    peanoRealSequenceLimit_eq (peano_second_dyadic_limit hRem e)
  rw [peanoMeasurableHessian_coe]
  by_cases hij : i=j
  · subst j
    simp only [peanoMeasurableMatrix,ite_true,hLimit]
  · simp only [peanoMeasurableMatrix,ite_eq_right hij,hLimit,peano_bilinear_pair B hB]
    ring

/-- Reconstruction is equality of the actual continuous bilinear maps. -/
theorem peanoMeasurableHessian_bilinear_of_peano {n : ℕ} {u : Point n → ℝ} {p : Point n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hB : ∀ v w, B v w=B w v)
    (hRem : (fun y => u (y,p.2)-u p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))
      =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) :
    autoBilinearMap n (peanoMeasurableHessian u p)=B := by
  ext v w
  have hv : (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) v • Yau.realVec i)=v := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).sum_repr' v
  have hw : (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) w • Yau.realVec i)=w := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).sum_repr' w
  rw [← hv,← hw]
  simp only [map_sum,map_smul,_root_.sum_apply,
    _root_.smul_apply,smul_eq_mul,autoBilinearMap_realVec,
    peanoMeasurableHessian_entries_of_peano hB hRem]

end Yau.LeafProofs.L05AutonomousAux
