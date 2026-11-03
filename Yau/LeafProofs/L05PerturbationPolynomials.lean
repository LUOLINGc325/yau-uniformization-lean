import Yau.LeafProofs.L05PerturbationGeometry
import Yau.LeafProofs.L09

open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbBilinear {n : ℕ} (A : Sym n) : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  ∑ i, ∑ j, (A : Mat n) i j •
    (innerSL ℝ (realVec i)).smulRight (innerSL ℝ (realVec j))

def perturbQuad {n : ℕ} (A : Sym n) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (A : Mat n) i j * inner ℝ (realVec i) x * inner ℝ (realVec j) x

def perturbPolynomial {n : ℕ} (c : ℝ) (b : Space n →L[ℝ] ℝ)
    (A : Sym n) (q : ℝ) (p : Point n) : ℝ :=
  c+b p.1+(1/2 : ℝ)*perturbQuad A p.1+q*p.2

theorem perturbBilinear_apply {n : ℕ} (A : Sym n) (v w : Space n) :
    perturbBilinear A v w = ∑ i, ∑ j,
      (A : Mat n) i j*inner ℝ (realVec i) v*inner ℝ (realVec j) w := by
  simp [perturbBilinear,ContinuousLinearMap.smulRight_apply,mul_assoc]

theorem perturbBilinear_symmetric {n : ℕ} (A : Sym n) (v w : Space n) :
    perturbBilinear A v w=perturbBilinear A w v := by
  classical
  have hA := (Matrix.isHermitian_iff_isSelfAdjoint.mpr A.property).isSymm
  rw [perturbBilinear_apply,perturbBilinear_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (A : Mat n) j i=(A : Mat n) i j from congrFun (congrFun hA i) j]
  ring

theorem perturb_realVec_inner {n : ℕ} (i j : RIdx n) :
    inner ℝ (realVec i) (realVec j)=if i=j then 1 else 0 := by
  simpa only [complexVector_realOrthonormalBasis_apply] using
    (complexVector_realOrthonormalBasis n).inner_eq_ite i j

theorem perturbBilinear_realVec {n : ℕ} (A : Sym n) (i j : RIdx n) :
    perturbBilinear A (realVec i) (realVec j)=(A : Mat n) i j := by
  classical
  simp [perturbBilinear_apply,perturb_realVec_inner]

theorem perturbQuad_eq_bilinear {n : ℕ} (A : Sym n) (x : Space n) :
    perturbQuad A x=perturbBilinear A x x := (perturbBilinear_apply A x x).symm

theorem perturb_quadratic_hasFDerivAt {n : ℕ} (A : Sym n) (x : Space n) :
    HasFDerivAt (fun y => (1/2 : ℝ)*perturbQuad A y) (perturbBilinear A x) x := by
  have h := ((perturbBilinear A).hasFDerivAt_of_bilinear
    (hasFDerivAt_id x) (hasFDerivAt_id x)).const_mul (1/2 : ℝ)
  convert h using 1
  · funext y
    rw [perturbQuad_eq_bilinear]
    rfl
  · ext v
    change perturbBilinear A x v=(1/2 : ℝ)*(perturbBilinear A x v+perturbBilinear A v x)
    rw [perturbBilinear_symmetric A v x]
    ring

theorem perturb_polynomial_spatial_hasFDerivAt {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q t : ℝ) (x : Space n) :
    HasFDerivAt (fun y => perturbPolynomial c b A q (y,t)) (b+perturbBilinear A x) x := by
  convert! ((b.hasFDerivAt.const_add c).add (perturb_quadratic_hasFDerivAt A x)).add_const (q*t) using 1

theorem perturb_polynomial_spatialD {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ) (p : Point n) :
    spatialD (perturbPolynomial c b A q) p=b+perturbBilinear A p.1 :=
  (perturb_polynomial_spatial_hasFDerivAt c b A q p.2 p.1).fderiv

theorem perturb_polynomial_spatialDD {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ) (p : Point n) :
    spatialDD (perturbPolynomial c b A q) p=perturbBilinear A := by
  have he : (fun x : Space n => spatialD (perturbPolynomial c b A q) (x,p.2)) =
      fun x => b+perturbBilinear A x := funext (fun x => perturb_polynomial_spatialD c b A q (x,p.2))
  change fderiv ℝ (fun x : Space n => spatialD (perturbPolynomial c b A q) (x,p.2)) p.1 = _
  rw [he]
  exact ((perturbBilinear A).hasFDerivAt.const_add b).fderiv

theorem perturb_polynomial_hessian {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ) (p : Point n) :
    hessian (perturbPolynomial c b A q) p=A := by
  unfold hessian
  simp only [perturb_polynomial_spatialDD,perturbBilinear_realVec]
  apply Subtype.ext
  exact IsSelfAdjoint.coe_selfAdjointPart_apply ℝ A.property


theorem perturb_polynomial_time_hasDerivAt {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q t : ℝ) (x : Space n) :
    HasDerivAt (fun s => perturbPolynomial c b A q (x,s)) q t := by
  convert! ((hasDerivAt_id t).const_mul q).const_add
    (c+b x+(1/2 : ℝ)*perturbQuad A x) using 1 <;> simp [perturbPolynomial]

theorem perturb_polynomial_timeD {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q R : ℝ) {p : Point n}
    (hp : p ∈ backward R) : timeD (backward R) (perturbPolynomial c b A q) p=q := by
  have hs : {s | (p.1,s) ∈ backward R}=Ioc (-(R^2)) 0 := by
    ext s
    simp [backward,hp.1]
  unfold timeD
  rw [hs]
  exact (perturb_polynomial_time_hasDerivAt c b A q p.2 p.1).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Ioc _ _ p.2 hp.2)

theorem perturb_polynomial_smooth {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ) :
    ContDiff ℝ ∞ (perturbPolynomial c b A q) := by
  have he : perturbPolynomial c b A q = fun p : Point n =>
      c+b p.1+(1/2 : ℝ)*perturbBilinear A p.1 p.1+q*p.2 := by
    funext p
    rw [perturbPolynomial,perturbQuad_eq_bilinear]
  rw [he]
  fun_prop

theorem perturb_polynomial_c2 {n : ℕ} (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q R : ℝ) :
    C2 (backward R) (perturbPolynomial c b A q) := by
  have hu := perturb_polynomial_smooth c b A q
  have hd : spatialD (perturbPolynomial c b A q)=fun p => b+perturbBilinear A p.1 :=
    funext (perturb_polynomial_spatialD c b A q)
  have hdd : spatialDD (perturbPolynomial c b A q)=fun _ => perturbBilinear A :=
    funext (perturb_polynomial_spatialDD c b A q)
  refine ⟨hu.continuous.continuousOn,?_,?_,?_,?_,?_⟩
  · rw [hd]
    fun_prop
  · rw [hdd]
    exact continuousOn_const
  · exact continuousOn_const.congr (fun p hp => perturb_polynomial_timeD c b A q R hp)
  · intro p hp
    exact (hu.contDiffAt.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  · intro p hp
    exact (perturb_polynomial_time_hasDerivAt c b A q p.2 p.1).differentiableAt.differentiableWithinAt

end Yau.LeafProofs.L05Aux
