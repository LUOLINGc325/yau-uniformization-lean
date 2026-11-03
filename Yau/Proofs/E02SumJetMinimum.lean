import Yau.Proofs.E02NormQuadraticJet
import Yau.Proofs.E02PeanoMinimum

open Set Filter Asymptotics
open scoped Topology Asymptotics
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D]

theorem realSecondJet_continuousLinearMap (p : D →L[ℝ] ℝ) (x : D) :
    RealSecondJet (fun y => p y) x p 0 := by
  refine ⟨fun _ _ => rfl,?_⟩
  have hz : (fun y => p y-p x-p (y-x)-(1/2)*(0 : D →L[ℝ] D →L[ℝ] ℝ) (y-x) (y-x)) =
      fun _ => 0 := by
    funext y
    simp
  rw [hz]
  exact isLittleO_zero _ _

/-- All factor jets are evaluated at projections of ONE product point.
Their actual local minimum yields both the common time-linear identity
and the full bilinear quadratic order before any epsilon/κ limit. -/
theorem sumJet_localMin_constraints {m : ℕ} (π : Fin m → D →L[ℝ] E)
    (f : Fin m → E → ℝ) (α : Fin m → ℝ) (Q : D)
    (p : Fin m → E →L[ℝ] ℝ) (A : Fin m → E →L[ℝ] E →L[ℝ] ℝ)
    (hJet : ∀ i, RealSecondJet (f i) (π i Q) (p i) (A i))
    (g : D → ℝ) (pg : D →L[ℝ] ℝ) (B : D →L[ℝ] D →L[ℝ] ℝ)
    (hg : RealSecondJet g Q pg B) (slope : D →L[ℝ] ℝ)
    (hMin : IsLocalMin (fun R => (∑ i, α i*f i (π i R))-g R-slope R) Q) :
    (∀ v, (∑ i, α i*p i (π i v)) = pg v+slope v) ∧
      ∀ v, B v v ≤ ∑ i, α i*A i (π i v) (π i v) := by
  let ps : D →L[ℝ] ℝ := ∑ i, α i • (p i).comp (π i)
  let As : D →L[ℝ] D →L[ℝ] ℝ := ∑ i, α i • (A i).bilinearComp (π i) (π i)
  have hEach (i : Fin m) : RealSecondJet (fun R => α i*f i (π i R)) Q
      (α i • (p i).comp (π i)) (α i • (A i).bilinearComp (π i) (π i)) :=
    realSecondJet_const_mul (realSecondJet_comp_continuousLinearMap (π i) (hJet i)) (α i)
  have hSum : RealSecondJet (fun R => ∑ i, α i*f i (π i R)) Q ps As :=
    realSecondJet_sum Finset.univ (fun i R => α i*f i (π i R)) Q
      (fun i => α i • (p i).comp (π i)) (fun i => α i • (A i).bilinearComp (π i) (π i))
      (fun i _ => hEach i)
  have hFull := realSecondJet_sub (realSecondJet_sub hSum hg)
    (realSecondJet_continuousLinearMap slope Q)
  have hLinear := realSecondJet_localMin_linear_zero hFull hMin
  have hQuadratic := realSecondJet_localMin_quadratic_nonneg hFull hMin
  constructor
  · intro v
    have hv := congrArg (fun L : D →L[ℝ] ℝ => L v) hLinear
    simp only [ps,sum_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,smul_eq_mul] at hv
    linarith
  · intro v
    have hv := hQuadratic v
    simp only [As,sum_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.zero_apply,smul_eq_mul] at hv
    linarith

end Yau.NodeProofs.E02Aux
