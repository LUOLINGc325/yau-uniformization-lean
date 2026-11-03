import Yau.Proofs.P06WeitzenbockQuadratic
import Yau.Proofs.G01RicciLocal

noncomputable section
open Filter
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

def jPullbackRealForm (A : RealForm M k) : RealForm M k :=
  fun x => (A x).compContinuousLinearMap (tangentJ x)

theorem jPullbackRealForm_apply (A : RealForm M k) (x : M.Carrier)
    (V : Fin k → TangentVector M x) :
    jPullbackRealForm A x V = A x (fun i => Complex.I • V i) := by
  rfl

theorem jPullbackRealForm_components (A : RealForm M k) (c : M.Carrier)
    (z : ComplexVector n) (I : Fin k → RIdx n) :
    formComponents (jPullbackRealForm A) c z I =
      (∏ r, jSign (I r)) * formComponents A c z (fun r => jIndex n (I r)) := by
  unfold formComponents
  rw [jPullbackRealForm_apply]
  have hv : (fun r => Complex.I • chartVec c (chartInv c z) (realVec (I r))) =
      fun r => jSign (I r) • chartVec c (chartInv c z) (realVec (jIndex n (I r))) := by
    funext r
    rw [← L12Aux.chartVec_complex_smul, I_smul_realVec, chartVec_real_smul]
  rw [hv, ContinuousAlternatingMap.map_smul_univ]
  rfl

theorem jPullbackRealForm_smooth (A : RealForm M k) (hA : SmoothRealForm A) :
    SmoothRealForm (jPullbackRealForm A) := by
  intro c I
  apply (contDiffOn_const.mul (hA c (fun r => jIndex n (I r)))).congr
  intro z _
  exact jPullbackRealForm_components A c z I

theorem jPullbackRealForm_support (A : RealForm M k) :
    closure {x | jPullbackRealForm A x ≠ 0} ⊆ closure {x | A x ≠ 0} := by
  apply closure_mono
  intro x hx hz
  apply hx
  apply ContinuousAlternatingMap.ext
  intro V
  rw [jPullbackRealForm_apply, hz]
  rfl

theorem jPullbackRealForm_compact (A : RealForm M k) (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (jPullbackRealForm A) :=
  hcA.of_isClosed_subset isClosed_closure (jPullbackRealForm_support A)

theorem jPullbackTwo_involution (A : RealForm M 2) :
    jPullbackRealForm (jPullbackRealForm A) = A := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro V
  rw [jPullbackRealForm_apply, jPullbackRealForm_apply]
  have hv : (fun i => Complex.I • (Complex.I • V i)) = fun i => (-1 : ℝ) • V i := by
    funext i
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hv, ContinuousAlternatingMap.map_smul_univ]
  norm_num only [Fin.prod_univ_two, neg_mul_neg, one_mul, one_smul]

theorem jPullbackRealForm_add (A B : RealForm M k) :
    jPullbackRealForm (A + B) = jPullbackRealForm A + jPullbackRealForm B := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro V
  simp only [jPullbackRealForm_apply, Pi.add_apply, ContinuousAlternatingMap.add_apply]

theorem jPullbackRealForm_smul (r : ℝ) (A : RealForm M k) :
    jPullbackRealForm (r • A) = r • jPullbackRealForm A := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro V
  simp only [jPullbackRealForm_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]

def oneOneProjection (A : RealForm M 2) : RealForm M 2 :=
  (1 / 2 : ℝ) • (A + jPullbackRealForm A)

theorem oneOneProjection_smooth (A : RealForm M 2) (hA : SmoothRealForm A) :
    SmoothRealForm (oneOneProjection A) :=
  L03.smoothRealForm_smul _ _
    (L03.smoothRealForm_add _ _ hA (jPullbackRealForm_smooth A hA))

theorem oneOneProjection_type (A : RealForm M 2) : RealOneOne (oneOneProjection A) := by
  have he : jPullbackRealForm (oneOneProjection A) = oneOneProjection A := by
    rw [oneOneProjection, jPullbackRealForm_smul, jPullbackRealForm_add,
      jPullbackTwo_involution, add_comm]
  intro x u v
  have hp := congrArg (fun F : RealForm M 2 => F x ![u,v]) he
  rw [jPullbackRealForm_apply] at hp
  have hv : (fun i : Fin 2 => Complex.I • (![u,v] i)) = ![Complex.I • u, Complex.I • v] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hp
  exact hp

theorem oneOneProjection_compact (A : RealForm M 2) (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (oneOneProjection A) :=
  L03.compactlySupportedRealForm_multiply (fun _ => (1 / 2 : ℝ)) _
    (L03.compactlySupportedRealForm_add _ _ hcA (jPullbackRealForm_compact A hcA))

end Yau.NodeProofs.P06Weitzenbock
