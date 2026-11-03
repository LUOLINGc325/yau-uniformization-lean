import Yau.LeafProofs.L16SpatialWordCalculus

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem fderiv_clm_const_eval {E V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {c : E → V →L[ℝ] W} {x : E} (hc : DifferentiableAt ℝ c x) (v : V) (e : E) :
    fderiv ℝ (fun y => c y v) x e = fderiv ℝ c x e v := by
  have h := congrArg (fun L : E →L[ℝ] W => L e)
    (fderiv_clm_apply hc (differentiableAt_const v))
  simpa only [fderiv_fun_const,Pi.zero_apply,zero_apply,ContinuousLinearMap.comp_zero,
    zero_add,ContinuousLinearMap.flip_apply] using h

theorem thirdFDeriv_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 3 g) (x e v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ g) y v w) x e =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x e v w := by
  have hD : ContDiff ℝ 2 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ g)) := hD.fderiv_right (by norm_num)
  have hDiff := hH.differentiable (by norm_num) x
  have h1 := fderiv_clm_const_eval hDiff v e
  have h2 := fderiv_clm_const_eval (hDiff.clm_apply (differentiableAt_const v)) w e
  rw [h1] at h2
  exact h2

theorem thirdFDeriv_swap_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 3 g) (x e v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x e v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x v e w := by
  have hD : ContDiff ℝ 2 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hD.contDiffAt.isSymmSndFDerivAt (by norm_num)) e v)

theorem thirdFDeriv_swap_last {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 3 g) (x e v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x e v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x e w v := by
  have hEq : (fun y => fderiv ℝ (fderiv ℝ g) y v w) =
      (fun y => fderiv ℝ (fderiv ℝ g) y w v) :=
    funext (fun y => (hg.contDiffAt.isSymmSndFDerivAt (by norm_num)) v w)
  have h := congrArg (fun f : E → ℝ => fderiv ℝ f x e) hEq
  simpa only [thirdFDeriv_eval hg] using h

theorem hessian_directional_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 3 g) (x e v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ g y e)) x v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x v w e := by
  have hD : ContDiff ℝ 2 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hGe : ContDiff ℝ 2 (fun y => fderiv ℝ g y e) := hD.clm_apply contDiff_const
  have hGeDiff := (hGe.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hEq : (fun y => fderiv ℝ (fun z => fderiv ℝ g z e) y w) =
      (fun y => fderiv ℝ (fderiv ℝ g) y w e) :=
    funext (fun y => fderiv_clm_const_eval (hD.differentiable (by norm_num) y) e w)
  calc
    _ = fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ g z e) y w) x v :=
      (fderiv_clm_const_eval hGeDiff w v).symm
    _ = fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ g) y w e) x v := by rw [hEq]
    _ = _ := thirdFDeriv_eval hg x v w e

/-- The third-order spatial commutation used in the source bootstrap,
with its finite differentiability hypothesis stated explicitly. -/
theorem directional_hessian_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 3 g) (x e v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ g) y v w) x e =
      fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ g y e)) x v w := by
  rw [thirdFDeriv_eval hg,hessian_directional_eval hg]
  exact (thirdFDeriv_swap_first hg x e v w).trans (thirdFDeriv_swap_last hg x v e w)

theorem directional_gradient_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 2 g) (x e v : E) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x e = fderiv ℝ (fun y => fderiv ℝ g y e) x v := by
  have hD : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  rw [fderiv_clm_const_eval (hD.differentiable (by norm_num) x) v e,
    fderiv_clm_const_eval (hD.differentiable (by norm_num) x) e v]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by norm_num)) e v

theorem spatialPartial_gradient_component_eq {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (e v : Space n) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) :
    spatialPartial (fun q => spatialD u q v) e p = spatialD (spatialPartial u e) p v :=
  directional_gradient_commute (c2_spatialSlice_contDiff hu hp.2) p.1 e v

theorem spatialPartial_hessian_component_eq {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hSlices : ∀ t ∈ Set.Icc 0 T, ContDiff ℝ 3 (fun x : Space n => u (x,t)))
    (e v w : Space n) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    spatialPartial (fun q => spatialDD u q v w) e p = spatialDD (spatialPartial u e) p v w :=
  directional_hessian_commute (hSlices p.2 hp.2) p.1 e v w

theorem spatial_gradient_component_differentiableAt {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (v : Space n) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) :
    DifferentiableAt ℝ (fun x : Space n => spatialD u (x,p.2) v) p.1 := by
  have hD : ContDiff ℝ 1 (fderiv ℝ (fun x : Space n => u (x,p.2))) :=
    (c2_spatialSlice_contDiff hu hp.2).fderiv_right (by norm_num)
  exact (hD.clm_apply (contDiff_const (c := v))).differentiable (by norm_num) p.1

theorem spatial_hessian_component_differentiableAt {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hSlices : ∀ t ∈ Set.Icc 0 T, ContDiff ℝ 3 (fun x : Space n => u (x,t)))
    (v w : Space n) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    DifferentiableAt ℝ (fun x : Space n => spatialDD u (x,p.2) v w) p.1 := by
  have hD : ContDiff ℝ 2 (fderiv ℝ (fun x : Space n => u (x,p.2))) :=
    (hSlices p.2 hp.2).fderiv_right (by norm_num)
  have hH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fun x : Space n => u (x,p.2)))) :=
    hD.fderiv_right (by norm_num)
  exact ((hH.clm_apply (contDiff_const (c := v))).clm_apply (contDiff_const (c := w))).differentiable
    (by norm_num) p.1

theorem holderBound_spatialPartial_hessian_component {n : ℕ} {α T C : ℝ} {u : Point n → ℝ}
    (hSlices : ∀ t ∈ Set.Icc 0 T, ContDiff ℝ 3 (fun x : Space n => u (x,t)))
    (e : Space n) (hPartial : SchauderBound α (cylinder Set.univ 0 T) (spatialPartial u e) C)
    (i j : Yau.RIdx n) :
    HolderBound α (cylinder Set.univ 0 T)
      (spatialPartial (fun p => spatialDD u p (Yau.realVec i) (Yau.realVec j)) e) C :=
  holderBound_congr_on (holderBound_hessian_component hPartial.2.2.2.1 i j)
    (fun _ hp => (spatialPartial_hessian_component_eq hSlices e (Yau.realVec i) (Yau.realVec j) hp).symm)

theorem holderBound_spatialPartial_gradient_component {n : ℕ} {α T C : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (e : Space n)
    (hPartial : HolderBound α (cylinder Set.univ 0 T)
      (fun p => (spatialPartial u e p,spatialD (spatialPartial u e) p)) C) (i : Yau.RIdx n) :
    HolderBound α (cylinder Set.univ 0 T) (spatialPartial (fun p => spatialD u p (Yau.realVec i)) e) C :=
  holderBound_congr_on (holderBound_gradient_component (holderBound_snd hPartial) i)
    (fun _ hp => (spatialPartial_gradient_component_eq hu e (Yau.realVec i) hp).symm)

end Yau.LeafProofs.L16Aux
