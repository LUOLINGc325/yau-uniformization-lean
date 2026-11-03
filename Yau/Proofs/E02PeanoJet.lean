import Yau.Blueprint.Nodes

open Set Filter Asymptotics
open scoped Topology Asymptotics
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual symmetric second Peano expansion. Its tensor is kept as
given by Aleksandrov; no second Frechet derivative of f is asserted. -/
def RealSecondJet (f : E → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  (∀ v w, A v w = A w v) ∧
  (fun y => f y-f x-p (y-x)-(1/2)*A (y-x) (y-x)) =o[𝓝 x] (fun y => ‖y-x‖^2)

theorem realSecondJet_const (c : ℝ) (x : E) : RealSecondJet (fun _ : E => c) x 0 0 := by
  refine ⟨fun _ _ => rfl,?_⟩
  simp

theorem realSecondJet_add {f g : E → ℝ} {x : E} {p q : E →L[ℝ] ℝ}
    {A B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : RealSecondJet f x p A) (hg : RealSecondJet g x q B) :
    RealSecondJet (fun y => f y+g y) x (p+q) (A+B) := by
  refine ⟨?_,?_⟩
  · intro v w
    simp only [add_apply]
    rw [hf.1 v w,hg.1 v w]
  · convert hf.2.add hg.2 using 1
    funext y
    simp only [add_apply]
    ring

theorem realSecondJet_const_mul {f : E → ℝ} {x : E} {p : E →L[ℝ] ℝ}
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hf : RealSecondJet f x p A) (c : ℝ) :
    RealSecondJet (fun y => c*f y) x (c • p) (c • A) := by
  refine ⟨?_,?_⟩
  · intro v w
    simp only [smul_apply,smul_eq_mul]
    rw [hf.1 v w]
  · convert hf.2.const_mul_left c using 1
    funext y
    simp only [smul_apply,smul_eq_mul]
    ring

theorem realSecondJet_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (p : ι → E →L[ℝ] ℝ) (A : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (h : ∀ i ∈ s, RealSecondJet (f i) x (p i) (A i)) :
    RealSecondJet (fun y => ∑ i ∈ s, f i y) x (∑ i ∈ s, p i) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using realSecondJet_const 0 x
  | @insert i s hi ih =>
    have hiJet := h i (Finset.mem_insert_self i s)
    have hsJet := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using realSecondJet_add hiJet hsJet

theorem norm_square_comp_continuousLinearMap_bigO (L : E →L[ℝ] F) (x : E) :
    (fun y => ‖L (y-x)‖^2) =O[𝓝 x] (fun y => ‖y-x‖^2) := by
  apply IsBigO.of_bound (‖L‖^2)
  apply Eventually.of_forall
  intro y
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖L (y-x)‖),
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖y-x‖)]
  have hLe := L.le_opNorm (y-x)
  have hN0 := norm_nonneg (L (y-x))
  have hN1 := norm_nonneg (y-x)
  have hNL := norm_nonneg L
  have hSq := (sq_le_sq₀ hN0 (mul_nonneg hNL hN1)).mpr hLe
  simpa only [mul_pow] using hSq

theorem realSecondJet_comp_continuousLinearMap
    {f : F → ℝ} {x : E} {p : F →L[ℝ] ℝ} {A : F →L[ℝ] F →L[ℝ] ℝ}
    (L : E →L[ℝ] F) (hf : RealSecondJet f (L x) p A) :
    RealSecondJet (fun y => f (L y)) x (p.comp L) (A.bilinearComp L L) := by
  refine ⟨?_,?_⟩
  · intro v w
    simp only [ContinuousLinearMap.bilinearComp_apply]
    exact hf.1 (L v) (L w)
  · have hComp := hf.2.comp_tendsto L.continuous.continuousAt.tendsto
    have hBound : (fun y => ‖L y-L x‖^2) =O[𝓝 x] (fun y => ‖y-x‖^2) := by
      simpa only [map_sub] using norm_square_comp_continuousLinearMap_bigO L x
    convert hComp.trans_isBigO hBound using 1
    funext y
    simp only [Function.comp_def,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.bilinearComp_apply,L.map_sub]

end Yau.NodeProofs.E02Aux
