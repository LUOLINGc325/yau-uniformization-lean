import Yau.Proofs.F03WirtingerDifferential

/-! Actual physical gradient triangle, product and scalar-chain bounds. -/
noncomputable section
open scoped ContDiff
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def physicalCovector (g : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) : ComplexVector n :=
  dualNormFactor (gMat g x) (realWirtingerMap n (fderiv ℝ (inChart x f) (chartPt x x)))

theorem sqrt_gradNormSq_eq_physicalCovector (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    Real.sqrt (gradNormSq g f x)=‖physicalCovector g f x‖ :=
  sqrt_gradNormSq_eq_factor_norm g f hf x

theorem smoothFn_center_differentiableAt {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    DifferentiableAt ℝ (inChart x f) (chartPt x x) :=
  ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_target x))).differentiableAt (by simp)

theorem physicalCovector_add (g : HermitianField M)
    {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier) :
    physicalCovector g (fun y => f y+q y) x=physicalCovector g f x+physicalCovector g q x := by
  unfold physicalCovector
  change dualNormFactor (gMat g x) (realWirtingerMap n
    (fderiv ℝ (fun z => inChart x f z+inChart x q z) (chartPt x x)))=_
  rw [fderiv_fun_add (smoothFn_center_differentiableAt hf x) (smoothFn_center_differentiableAt hq x),
    map_add,map_add]

theorem physicalCovector_mul (g : HermitianField M)
    {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier) :
    physicalCovector g (fun y => f y*q y) x=f x • physicalCovector g q x+q x • physicalCovector g f x := by
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  unfold physicalCovector
  change dualNormFactor (gMat g x) (realWirtingerMap n
    (fderiv ℝ (fun z => inChart x f z*inChart x q z) (chartPt x x)))=_
  rw [fderiv_fun_mul (smoothFn_center_differentiableAt hf x) (smoothFn_center_differentiableAt hq x),
    map_add,map_add,map_smul,map_smul,map_smul,map_smul]
  simp only [inChart,hinv]

theorem physicalCovector_scalar_comp (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (F : ℝ → ℝ) (x : M.Carrier)
    (hF : DifferentiableAt ℝ F (f x)) :
    physicalCovector g (fun y => F (f y)) x=deriv F (f x) • physicalCovector g f x := by
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hF' : HasDerivAt F (deriv F (f x)) (inChart x f (chartPt x x)) := by
    simpa only [inChart,hinv] using hF.hasDerivAt
  have hD := hF'.comp_hasFDerivAt (chartPt x x) (smoothFn_center_differentiableAt hf x).hasFDerivAt
  unfold physicalCovector
  change dualNormFactor (gMat g x) (realWirtingerMap n
    (fderiv ℝ (F ∘ inChart x f) (chartPt x x)))=_
  rw [hD.fderiv,map_smul,map_smul]

theorem sqrt_gradNormSq_add_le (g : HermitianField M)
    {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => f y+q y) x) ≤
      Real.sqrt (gradNormSq g f x)+Real.sqrt (gradNormSq g q x) := by
  have hAdd : SmoothFn (fun y => f y+q y) := fun a => (hf a).add (hq a)
  rw [sqrt_gradNormSq_eq_physicalCovector g hAdd,
    sqrt_gradNormSq_eq_physicalCovector g hf,sqrt_gradNormSq_eq_physicalCovector g hq,
    physicalCovector_add g hf hq]
  exact norm_add_le _ _

theorem sqrt_gradNormSq_mul_le (g : HermitianField M)
    {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => f y*q y) x) ≤
      |f x| * Real.sqrt (gradNormSq g q x)+|q x| * Real.sqrt (gradNormSq g f x) := by
  have hMul : SmoothFn (fun y => f y*q y) := fun a => (hf a).mul (hq a)
  rw [sqrt_gradNormSq_eq_physicalCovector g hMul,
    sqrt_gradNormSq_eq_physicalCovector g hf,sqrt_gradNormSq_eq_physicalCovector g hq,
    physicalCovector_mul g hf hq]
  simpa only [norm_smul,Real.norm_eq_abs] using
    norm_add_le (f x • physicalCovector g q x) (q x • physicalCovector g f x)

theorem sqrt_gradNormSq_scalar_comp (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => F (f y)) x)=
      |deriv F (f x)| * Real.sqrt (gradNormSq g f x) := by
  have hComp : SmoothFn (fun y => F (f y)) := fun a => hF.comp_contDiffOn (hf a)
  rw [sqrt_gradNormSq_eq_physicalCovector g hComp,
    sqrt_gradNormSq_eq_physicalCovector g hf,
    physicalCovector_scalar_comp g hf F x (hF.differentiable (by simp) _),norm_smul,Real.norm_eq_abs]

theorem physicalCovector_sum {ι : Type*} (g : HermitianField M) (S : Finset ι)
    (f : ι → M.Carrier → ℝ) (hf : ∀ i ∈ S,SmoothFn (f i)) (x : M.Carrier) :
    physicalCovector g (fun y => ∑ i ∈ S,f i y) x=∑ i ∈ S,physicalCovector g (f i) x := by
  unfold physicalCovector
  change dualNormFactor (gMat g x) (realWirtingerMap n
    (fderiv ℝ (fun z => ∑ i ∈ S,inChart x (f i) z) (chartPt x x)))=_
  rw [fderiv_fun_sum (fun i hi => smoothFn_center_differentiableAt (hf i hi) x),map_sum,map_sum]

theorem sqrt_gradNormSq_sum_le {ι : Type*} (g : HermitianField M) (S : Finset ι)
    (f : ι → M.Carrier → ℝ) (hf : ∀ i ∈ S,SmoothFn (f i)) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => ∑ i ∈ S,f i y) x) ≤
      ∑ i ∈ S,Real.sqrt (gradNormSq g (f i) x) := by
  have hSum : SmoothFn (fun y => ∑ i ∈ S,f i y) :=
    fun a => ContDiffOn.sum (fun i hi => hf i hi a)
  rw [sqrt_gradNormSq_eq_physicalCovector g hSum,physicalCovector_sum g S f hf]
  calc
    _ ≤ ∑ i ∈ S,‖physicalCovector g (f i) x‖ := norm_sum_le _ _
    _ = _ := Finset.sum_congr rfl (fun i hi => (sqrt_gradNormSq_eq_physicalCovector g (hf i hi) x).symm)

end Yau.Proofs.F03Aux
