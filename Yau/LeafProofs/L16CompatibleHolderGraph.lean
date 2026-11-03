import Yau.LeafProofs.L16HolderOnlyEstimates

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

local instance compatibleHolderGraph_baseNormedAddCommGroup {n : ℕ} (α : ℝ)
    (Q : Set (Point n)) : NormedAddCommGroup (holderGraph α Q) := inferInstance
local instance compatibleHolderGraph_baseNormedSpace {n : ℕ} (α : ℝ)
    (Q : Set (Point n)) : NormedSpace ℝ (holderGraph α Q) := inferInstance

theorem compatibleHolderGraph_eval_continuous {n : ℕ} {α : ℝ} {Q : Set (Point n)}
    (p : Point n) : Continuous (fun u : holderGraph α Q => holderGraphFun u p) := by
  classical
  by_cases hp : p ∈ Q
  · simpa [holderGraphFun, hp, BoundedContinuousFunction.evalCLM, Function.comp_def] using
      (BoundedContinuousFunction.evalCLM ℝ (⟨p,hp⟩ : Q)).continuous.comp
        (continuous_fst.comp continuous_subtype_val)
  · simpa only [holderGraphFun, dite_eq_right hp] using
      (continuous_const : Continuous (fun _ : holderGraph α Q => (0 : ℝ)))

/-- Only the initial lateral corner is constrained. -/
def compatibleHolderGraph {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    Submodule ℝ (holderGraph α (cylinder (closure O) 0 T)) where
  carrier := {u | ∀ x ∈ frontier O, holderGraphFun u (x,0) = 0}
  zero_mem' := by intro x hx; simp [holderGraphFun_zero]
  add_mem' := by
    intro u v hu hv x hx
    simp only [holderGraphFun_add, Pi.add_apply, hu x hx, hv x hx, add_zero]
  smul_mem' := by
    intro a u hu x hx
    simp only [holderGraphFun_smul, Pi.smul_apply, smul_eq_mul, hu x hx, mul_zero]

instance compatibleHolderGraph_normedAddCommGroup {n : ℕ} (α : ℝ)
    (O : Set (Space n)) (T : ℝ) : NormedAddCommGroup (compatibleHolderGraph α O T) :=
  inferInstance

instance compatibleHolderGraph_normedSpace {n : ℕ} (α : ℝ)
    (O : Set (Space n)) (T : ℝ) : NormedSpace ℝ (compatibleHolderGraph α O T) :=
  inferInstance

theorem compatibleHolderGraph_isClosed {n : ℕ} (α : ℝ)
    (O : Set (Space n)) (T : ℝ) :
    IsClosed (compatibleHolderGraph α O T :
      Set (holderGraph α (cylinder (closure O) 0 T))) := by
  change IsClosed {u : holderGraph α (cylinder (closure O) 0 T) |
    ∀ x ∈ frontier O, holderGraphFun u (x,0) = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro hx
  exact isClosed_eq (compatibleHolderGraph_eval_continuous (x,0)) continuous_const

instance compatibleHolderGraph_completeSpace {n : ℕ} (α : ℝ)
    (O : Set (Space n)) (T : ℝ) : CompleteSpace (compatibleHolderGraph α O T) :=
  (compatibleHolderGraph_isClosed α O T).completeSpace_coe

def compatibleHolderFun {n : ℕ} {α T : ℝ} {O : Set (Space n)}
    (u : compatibleHolderGraph α O T) : Point n → ℝ := holderGraphFun u.val

theorem compatibleHolderFun_holderBound {n : ℕ} {α T : ℝ} {O : Set (Space n)}
    (u : compatibleHolderGraph α O T) :
    HolderBound α (cylinder (closure O) 0 T) (compatibleHolderFun u) ‖u‖ :=
  holderGraphFun_holderBound u.val

theorem compatibleHolderFun_corner {n : ℕ} {α T : ℝ} {O : Set (Space n)}
    (u : compatibleHolderGraph α O T) {x : Space n} (hx : x ∈ frontier O) :
    compatibleHolderFun u (x,0) = 0 := u.property x hx

theorem compatibleHolderFun_zero {n : ℕ} {α T : ℝ} {O : Set (Space n)} :
    compatibleHolderFun (0 : compatibleHolderGraph α O T) = 0 := holderGraphFun_zero

theorem compatibleHolderFun_add {n : ℕ} {α T : ℝ} {O : Set (Space n)}
    (u v : compatibleHolderGraph α O T) :
    compatibleHolderFun (u+v) = compatibleHolderFun u+compatibleHolderFun v :=
  holderGraphFun_add u.val v.val

theorem compatibleHolderFun_smul {n : ℕ} {α T : ℝ} {O : Set (Space n)}
    (a : ℝ) (u : compatibleHolderGraph α O T) :
    compatibleHolderFun (a • u) = a • compatibleHolderFun u := holderGraphFun_smul a u.val

def compatibleHolderGraphOfBound {n : ℕ} {α T C : ℝ} {O : Set (Space n)}
    {f : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hf : HolderBound α (cylinder (closure O) 0 T) f C)
    (hcorner : ∀ x ∈ frontier O, f (x,0) = 0) : compatibleHolderGraph α O T :=
  ⟨holderGraphOfBound hα hf, by
    intro x hx
    rw [holderGraphOfBound_eqOn hα hf ⟨hx.1, le_rfl, hT⟩]
    exact hcorner x hx⟩

theorem compatibleHolderGraphOfBound_norm_le {n : ℕ} {α T C : ℝ} {O : Set (Space n)}
    {f : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hf : HolderBound α (cylinder (closure O) 0 T) f C)
    (hcorner : ∀ x ∈ frontier O, f (x,0) = 0) :
    ‖compatibleHolderGraphOfBound hα hT hf hcorner‖ ≤ C :=
  holderGraphOfBound_norm_le hα hf

theorem compatibleHolderGraphOfBound_eqOn {n : ℕ} {α T C : ℝ} {O : Set (Space n)}
    {f : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hf : HolderBound α (cylinder (closure O) 0 T) f C)
    (hcorner : ∀ x ∈ frontier O, f (x,0) = 0) :
    Set.EqOn (compatibleHolderFun (compatibleHolderGraphOfBound hα hT hf hcorner)) f
      (cylinder (closure O) 0 T) := holderGraphOfBound_eqOn hα hf

def compatibleHolderGraphLift {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α T C : ℝ} {O : Set (Space n)}
    (hα : 0 < α) (hT : 0 ≤ T) (F : E → Point n → ℝ)
    (hBound : ∀ x, HolderBound α (cylinder (closure O) 0 T) (F x) (C*‖x‖))
    (hAdd : ∀ x y, ∀ p ∈ cylinder (closure O) 0 T, F (x+y) p = F x p+F y p)
    (hSmul : ∀ (a : ℝ) x, ∀ p ∈ cylinder (closure O) 0 T, F (a • x) p = a*F x p)
    (hcorner : ∀ v x, x ∈ frontier O → F v (x,0) = 0) :
    E →L[ℝ] compatibleHolderGraph α O T :=
  (holderGraphLift hα F hBound hAdd hSmul).codRestrict (compatibleHolderGraph α O T)
    (by
      intro v x hx
      change holderGraphFun (holderGraphOfBound hα (hBound v)) (x,0) = 0
      rw [holderGraphOfBound_eqOn hα (hBound v) ⟨hx.1, le_rfl, hT⟩]
      exact hcorner v x hx)

theorem compatibleHolderGraphLift_eqOn {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α T C : ℝ} {O : Set (Space n)}
    (hα : 0 < α) (hT : 0 ≤ T) (F : E → Point n → ℝ)
    (hBound : ∀ x, HolderBound α (cylinder (closure O) 0 T) (F x) (C*‖x‖))
    (hAdd : ∀ x y, ∀ p ∈ cylinder (closure O) 0 T, F (x+y) p = F x p+F y p)
    (hSmul : ∀ (a : ℝ) x, ∀ p ∈ cylinder (closure O) 0 T, F (a • x) p = a*F x p)
    (hcorner : ∀ v x, x ∈ frontier O → F v (x,0) = 0) (v : E) :
    Set.EqOn (compatibleHolderFun (compatibleHolderGraphLift hα hT F hBound hAdd hSmul hcorner v))
      (F v) (cylinder (closure O) 0 T) := holderGraphOfBound_eqOn hα (hBound v)

theorem compatibleHolderGraphLift_norm_le {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α T C : ℝ} {O : Set (Space n)}
    (hα : 0 < α) (hT : 0 ≤ T) (F : E → Point n → ℝ)
    (hBound : ∀ x, HolderBound α (cylinder (closure O) 0 T) (F x) (C*‖x‖))
    (hAdd : ∀ x y, ∀ p ∈ cylinder (closure O) 0 T, F (x+y) p = F x p+F y p)
    (hSmul : ∀ (a : ℝ) x, ∀ p ∈ cylinder (closure O) 0 T, F (a • x) p = a*F x p)
    (hcorner : ∀ v x, x ∈ frontier O → F v (x,0) = 0) (v : E) :
    ‖compatibleHolderGraphLift hα hT F hBound hAdd hSmul hcorner v‖ ≤ C*‖v‖ :=
  holderGraphLift_norm_le hα F hBound hAdd hSmul v

theorem compatibleHolderGraphLift_opNorm_le {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α T C : ℝ} {O : Set (Space n)}
    (hα : 0 < α) (hT : 0 ≤ T) (hC : 0 ≤ C) (F : E → Point n → ℝ)
    (hBound : ∀ x, HolderBound α (cylinder (closure O) 0 T) (F x) (C*‖x‖))
    (hAdd : ∀ x y, ∀ p ∈ cylinder (closure O) 0 T, F (x+y) p = F x p+F y p)
    (hSmul : ∀ (a : ℝ) x, ∀ p ∈ cylinder (closure O) 0 T, F (a • x) p = a*F x p)
    (hcorner : ∀ v x, x ∈ frontier O → F v (x,0) = 0) :
    ‖compatibleHolderGraphLift hα hT F hBound hAdd hSmul hcorner‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (compatibleHolderGraphLift_norm_le hα hT F hBound hAdd hSmul hcorner)


theorem compatibleHolderGraph_residual_correction_weighted {n : ℕ} {α : ℝ} {O : Set (Space n)} {T : ℝ}
    (R : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α O T) {B : ℝ} (hB : 0 ≤ B)
    (hContract : ∀ x, ‖R x‖+B*‖(R x).val.val.1‖ ≤
      (1/2 : ℝ)*(‖x‖+B*‖x.val.val.1‖)) (f : compatibleHolderGraph α O T) :
    ∃ g : compatibleHolderGraph α O T, g+R g = f ∧ ‖g‖ ≤ 2*(1+B)*‖f‖ := by
  let N : compatibleHolderGraph α O T → ℝ := fun x => ‖x‖+B*‖x.val.val.1‖
  have hN (x : compatibleHolderGraph α O T) : ‖x‖ ≤ N x := by
    dsimp only [N]
    exact le_add_of_nonneg_right (mul_nonneg hB (norm_nonneg _))
  have hNeg (x : compatibleHolderGraph α O T) : N (-x) = N x := by
    simp only [N,norm_neg,Submodule.coe_neg,Prod.fst_neg]
  let v : ℕ → compatibleHolderGraph α O T := fun k => (fun x => -R x)^[k] f
  have hv0 : v 0 = f := rfl
  have hvSucc (k : ℕ) : v (k+1) = -R (v k) :=
    Function.iterate_succ_apply' (fun x => -R x) k f
  have hvSize (k : ℕ) : N (v k) ≤ (1/2 : ℝ)^k*N f := by
    induction k with
    | zero => simp only [hv0,pow_zero,one_mul,le_refl]
    | succ k ih =>
      rw [hvSucc,hNeg]
      calc
        N (R (v k)) ≤ (1/2 : ℝ)*N (v k) := hContract _
        _ ≤ (1/2 : ℝ)*((1/2 : ℝ)^k*N f) := by gcongr
        _ = (1/2 : ℝ)^(k+1)*N f := by ring
  have hvBound (k : ℕ) : ‖v k‖ ≤ (1/2 : ℝ)^k*N f := (hN _).trans (hvSize k)
  have hGeom : Summable (fun k : ℕ => (1/2 : ℝ)^k*N f) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hvSum : Summable v := hGeom.of_norm_bounded hvBound
  refine ⟨∑' k, v k,?_,?_⟩
  · have hTail : (∑' k, v (k+1)) = -R (∑' k, v k) := by
      simp_rw [hvSucc]
      rw [tsum_neg,← R.map_tsum hvSum]
    have hSum := hvSum.tsum_eq_zero_add
    rw [hv0,hTail] at hSum
    exact eq_sub_iff_add_eq.mp hSum
  · have hBound : ‖∑' k, v k‖ ≤ 2*N f := by
      apply tsum_of_norm_bounded _ hvBound
      convert hGeom.hasSum using 1
      rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    have hProjection : ‖f.val.val.1‖ ≤ ‖f‖ := by
      change ‖f.val.val.1‖ ≤ max ‖f.val.val.1‖ ‖f.val.val.2‖
      exact le_max_left _ _
    calc
      _ ≤ 2*N f := hBound
      _ ≤ 2*(1+B)*‖f‖ := by dsimp only [N]; nlinarith

/-- The large supremum coefficient is absorbed into a weight chosen after the
    cutoff radius; no smallness requirement on its product with ε is used. -/
theorem compatibleHolderGraph_residual_correction_of_two_bounds {n : ℕ} {α : ℝ}
    {O : Set (Space n)} {T : ℝ} (R : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α O T)
    {ε A d B : ℝ} (hB : 0 ≤ B) (hεd : ε+B*d ≤ (1/2 : ℝ))
    (hAB : A ≤ B/2)
    (hStrong : ∀ x, ‖R x‖ ≤ ε*‖x‖+A*‖x.val.val.1‖)
    (hSup : ∀ x, ‖(R x).val.val.1‖ ≤ d*‖x‖) (f : compatibleHolderGraph α O T) :
    ∃ g : compatibleHolderGraph α O T, g+R g = f ∧ ‖g‖ ≤ 2*(1+B)*‖f‖ := by
  apply compatibleHolderGraph_residual_correction_weighted R hB _ f
  intro x
  have h := add_le_add (hStrong x) (mul_le_mul_of_nonneg_left (hSup x) hB)
  have h1 := mul_le_mul_of_nonneg_right hεd (norm_nonneg x)
  have h2 := mul_le_mul_of_nonneg_right hAB (norm_nonneg x.val.val.1)
  nlinarith

/-- Choose the weight after the potentially large supremum coefficient. -/
theorem compatibleHolderGraph_residual_correction_of_small_two_bounds {n : ℕ} {α : ℝ}
    {O : Set (Space n)} {T : ℝ} (R : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α O T)
    {ε A d : ℝ} (hε : ε ≤ (1/4 : ℝ)) (_hA : 0 ≤ A)
    (hd : d ≤ 1/(4*max 1 (4*A)))
    (hStrong : ∀ x, ‖R x‖ ≤ ε*‖x‖+A*‖x.val.val.1‖)
    (hSup : ∀ x, ‖(R x).val.val.1‖ ≤ d*‖x‖) (f : compatibleHolderGraph α O T) :
    ∃ g : compatibleHolderGraph α O T, g+R g = f ∧ ‖g‖ ≤ 2*(1+max 1 (4*A))*‖f‖ := by
  have hB : 0 < max 1 (4*A) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hBd := (le_div_iff₀ (by positivity : 0 < 4*max 1 (4*A))).mp hd
  have hAB : A ≤ max 1 (4*A)/2 := by linarith [le_max_right (1 : ℝ) (4*A)]
  exact compatibleHolderGraph_residual_correction_of_two_bounds R hB.le
    (by nlinarith) hAB hStrong hSup f

end Yau.LeafProofs.L16Aux
