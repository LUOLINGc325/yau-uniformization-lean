import Yau.Proofs.E02EuclideanPacking
import Yau.Proofs.E02StrictHessian

open Set Filter
open scoped Topology ContDiff Asymptotics InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

/-- Sum-of-squares real coordinates for the physical base and time. -/
def baseTimeRealCoordinates (n : ℕ) : (ComplexVector n × ℝ) ≃L[ℝ]
    EuclideanSpace ℝ (Fin (2*n+1)) :=
  ((complexRealCoordinates n).toContinuousLinearEquiv.prodCongr timeRealCoordinates).trans
    (euclideanJoin (2*n) 1)

theorem baseTimeRealCoordinates_norm_sq (n : ℕ) (p : ComplexVector n × ℝ) :
    ‖baseTimeRealCoordinates n p‖^2 = ‖p.1‖^2+p.2^2 := by
  simp only [baseTimeRealCoordinates,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    euclideanJoin_norm_sq,LinearIsometryEquiv.norm_map,timeRealCoordinates_norm_sq]

/-- Strictification takes place in Euclidean packed coordinates. The
ordinary product carries its genuine max norm throughout. -/
def baseTimeStrictify {n : ℕ} (f : ComplexVector n × ℝ → ℝ) (a p : ComplexVector n × ℝ) : ℝ :=
  strictifyTest (fun q => f ((baseTimeRealCoordinates n).symm q))
    (baseTimeRealCoordinates n a) (baseTimeRealCoordinates n p)

theorem baseTimeStrictify_at {n : ℕ} (f : ComplexVector n × ℝ → ℝ) (a : ComplexVector n × ℝ) :
    baseTimeStrictify f a a = f a := by
  simp [baseTimeStrictify,strictifyTest]

theorem baseTimeStrictify_le {n : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (a p : ComplexVector n × ℝ) : baseTimeStrictify f a p ≤ f p := by
  simpa only [baseTimeStrictify,ContinuousLinearEquiv.symm_apply_apply] using
    strictifyTest_le (fun q => f ((baseTimeRealCoordinates n).symm q))
      (baseTimeRealCoordinates n a) (baseTimeRealCoordinates n p)

theorem baseTimeStrictify_strict_lower {n : ℕ} {f g : ComplexVector n × ℝ → ℝ}
    {a p : ComplexVector n × ℝ} (hLower : f p ≤ g p) (hNe : p ≠ a) :
    baseTimeStrictify f a p < g p := by
  have hNe' : baseTimeRealCoordinates n p ≠ baseTimeRealCoordinates n a :=
    fun hEq => hNe ((baseTimeRealCoordinates n).injective hEq)
  simpa only [baseTimeStrictify,ContinuousLinearEquiv.symm_apply_apply] using
    strictifyTest_strict_lower
      (f := fun q => f ((baseTimeRealCoordinates n).symm q))
      (L := fun q => g ((baseTimeRealCoordinates n).symm q))
      (x := baseTimeRealCoordinates n a) (y := baseTimeRealCoordinates n p)
      (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hLower) hNe'

theorem baseTimeStrictify_contDiffAt {n : ℕ} {f : ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ℝ} (hf : ContDiffAt ℝ ∞ f a) :
    ContDiffAt ℝ ∞ (baseTimeStrictify f a) a := by
  have hQ : ContDiff ℝ ∞ (fun p : ComplexVector n × ℝ =>
      ‖baseTimeRealCoordinates n p-baseTimeRealCoordinates n a‖^4) := by
    have hSq : ContDiff ℝ ∞ (fun p : ComplexVector n × ℝ =>
        ‖baseTimeRealCoordinates n p-baseTimeRealCoordinates n a‖^2) :=
      ((baseTimeRealCoordinates n).contDiff.sub contDiff_const).norm_sq ℝ
    simpa only [←pow_mul] using hSq.pow 2
  have hEq : baseTimeStrictify f a = (fun p => f p-
      ‖baseTimeRealCoordinates n p-baseTimeRealCoordinates n a‖^4) := by
    funext p
    simp [baseTimeStrictify,strictifyTest]
  rw [hEq]
  exact hf.sub hQ.contDiffAt

/-- The genuine Peano coefficients on the original max-norm product
agree with those of f, by affine transport through the Euclidean chart. -/
theorem baseTimeStrictify_realSecondJet {n : ℕ} {f : ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ℝ} (hf : ContDiffAt ℝ 2 f a) :
    RealSecondJet (baseTimeStrictify f a) a (fderiv ℝ f a) (fderiv ℝ (fderiv ℝ f) a) := by
  let e := baseTimeRealCoordinates n
  have hPacked : ContDiffAt ℝ 2 (fun q => f (e.symm q)) (e a) := by
    have hf' : ContDiffAt ℝ 2 f (e.symm (e a)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
    exact hf'.comp (e a) e.symm.contDiff.contDiffAt
  have hJet := realSecondJet_of_contDiffAt_two hPacked
  have hOriginal := realSecondJet_comp_continuousLinearMap e.toContinuousLinearMap hJet
  have hOriginal' : RealSecondJet f a
      ((fderiv ℝ (fun q => f (e.symm q)) (e a)).comp e.toContinuousLinearMap)
      ((fderiv ℝ (fderiv ℝ (fun q => f (e.symm q))) (e a)).bilinearComp
        e.toContinuousLinearMap e.toContinuousLinearMap) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.coe_coe] using hOriginal
  have hUnique := realSecondJet_unique hOriginal' (realSecondJet_of_contDiffAt_two hf)
  have hStrict := realSecondJet_comp_continuousLinearMap e.toContinuousLinearMap
    (realSecondJet_strictify hJet)
  rw [hUnique.1,hUnique.2] at hStrict
  convert hStrict using 1
  rfl

end Yau.NodeProofs.E02Aux
