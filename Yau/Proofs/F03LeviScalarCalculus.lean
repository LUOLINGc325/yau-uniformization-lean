import Yau.Proofs.F03LeviProductCalculus
import Yau.Proofs.F03GradientAlgebra
import Yau.LeafProofs.L17RicciNaturality

/-! The actual scalar Levi rules in the chart centered at the original manifold point. -/
noncomputable section
open scoped Topology ContDiff ComplexOrder Matrix
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def scalarFirstCovector (f : M.Carrier → ℝ) (x : M.Carrier) : Fin n → ℂ :=
  realFirstCovector (inChart x f) (chartPt x x)

theorem scalarFirstCovector_dualNorm (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    dualNormMat (gMat g x) (WithLp.toLp 2 (scalarFirstCovector f x))=gradNormSq g f x := by
  rw [scalarFirstCovector,realFirstCovector_eq,WithLp.toLp_ofLp,
    realWirtingerMap_fderiv (inChart x f) (chartPt x x) (smoothFn_center_differentiableAt hf x)]
  rfl

theorem smoothFn_center_contDiffAt_two {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
  ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_target x))).of_le (by simp)

theorem levi_real_add {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier) :
    levi (fun y => f y+q y) x=levi f x+levi q x :=
  LeafProofs.L17Aux.leviC_add (smoothFn_center_contDiffAt_two hf x) (smoothFn_center_contDiffAt_two hq x)

theorem levi_real_const_mul {f : M.Carrier → ℝ} (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    levi (fun y => c*f y) x=(c:ℂ) • levi f x :=
  LeafProofs.L17Aux.leviC_const_mul (smoothFn_center_contDiffAt_two hf x) c

theorem levi_real_mul {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier) :
    levi (fun y => f y*q y) x=(f x:ℂ) • levi q x+(q x:ℂ) • levi f x+
      Matrix.vecMulVec (star (scalarFirstCovector f x)) (scalarFirstCovector q x)+
      Matrix.vecMulVec (star (scalarFirstCovector q x)) (scalarFirstCovector f x) := by
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  change leviC (fun z => inChart x f z*inChart x q z) (chartPt x x)=_
  simpa only [levi,scalarFirstCovector,inChart,hinv] using
    leviC_real_mul (smoothFn_center_contDiffAt_two hf x) (smoothFn_center_contDiffAt_two hq x)

theorem levi_real_scalar_comp {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : M.Carrier) :
    levi (fun y => F (f y)) x=Complex.ofReal (deriv F (f x)) • levi f x+
      Complex.ofReal (deriv (deriv F) (f x)) •
        Matrix.vecMulVec (star (scalarFirstCovector f x)) (scalarFirstCovector f x) := by
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hOuter : ContDiffAt ℝ 2 F (inChart x f (chartPt x x)) := by
    simpa only [inChart,hinv] using (hF.contDiffAt (x := f x)).of_le (by simp : (2:ℕ∞ω) ≤ ∞)
  change leviC (F ∘ inChart x f) (chartPt x x)=_
  simpa only [levi,scalarFirstCovector,inChart,hinv,Function.comp_def] using
    leviC_real_scalar_comp (smoothFn_center_contDiffAt_two hf x) hOuter

theorem levi_real_sum {ι : Type*} (f : ι → M.Carrier → ℝ) (hf : ∀ i,SmoothFn (f i))
    (S : Finset ι) (x : M.Carrier) :
    levi (fun y => ∑ i ∈ S,f i y) x=∑ i ∈ S,levi (f i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change leviC (fun _ => (0:ℝ)) (chartPt x x)=0
    exact LeafProofs.L17Aux.leviC_const (0:ℝ) (chartPt x x)
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hSum : SmoothFn (fun y => ∑ j ∈ S,f j y) := fun a => ContDiffOn.sum (fun j _ => hf j a)
    rw [levi_real_add (hf i) hSum,ih]

end Yau.Proofs.F03Aux
