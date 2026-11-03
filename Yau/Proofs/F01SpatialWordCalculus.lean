import Yau.Proofs.F01SpatialDerivativeWords

/-! Slice-wise smoothness and exact linear calculus for finite native
spatial words. A finite list derivative rule retains multiplicities in
subsequent commutator expansions. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F G ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem hasFDerivAt_list_sum_native (l : List ι) (f : ι → E → F) (D : ι → E →L[ℝ] F)
    {x : E} (hf : ∀ i ∈ l, HasFDerivAt (f i) (D i) x) :
    HasFDerivAt (fun z => (l.map (fun i => f i z)).sum) (l.map D).sum x := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using hasFDerivAt_const (𝕜 := ℝ) (0 : F) x
  | cons a l ih =>
    have ha := hf a (by simp)
    have hl := ih (fun i hi => hf i (by simp [hi]))
    simpa only [List.map_cons, List.sum_cons] using ha.fun_add hl

theorem spatialDerivativeWord_smooth_slice {f : E × ℝ → F} {S : Set E} {t : ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (fun x => f (x, t)) S) (vs : List E) :
    ContDiffOn ℝ ∞ (fun x => spatialDerivativeWord vs f (x, t)) S := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    exact (ih.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

theorem spatialDerivativeWord_add_slice {f g : E × ℝ → F} {S : Set E} {t : ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (fun x => f (x, t)) S)
    (hg : ContDiffOn ℝ ∞ (fun x => g (x, t)) S) (vs : List E)
    {x : E} (hx : x ∈ S) :
    spatialDerivativeWord vs (fun p => f p + g p) (x, t) =
      spatialDerivativeWord vs f (x, t) + spatialDerivativeWord vs g (x, t) := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : (fun z => spatialDerivativeWord vs (fun p => f p + g p) (z, t)) =ᶠ[𝓝 x]
        (fun z => spatialDerivativeWord vs f (z, t) + spatialDerivativeWord vs g (z, t)) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact ih hz
    change fderiv ℝ (fun z => spatialDerivativeWord vs (fun p => f p + g p) (z, t)) x v = _
    rw [he.fderiv_eq, fderiv_fun_add
      (((spatialDerivativeWord_smooth_slice hS hf vs).contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp))
      (((spatialDerivativeWord_smooth_slice hS hg vs).contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp))]
    rfl

theorem spatialDerivativeWord_clm_slice {f : E × ℝ → F} {S : Set E} {t : ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ (fun x => f (x, t)) S)
    (L : F →L[ℝ] G) (vs : List E) {x : E} (hx : x ∈ S) :
    spatialDerivativeWord vs (fun p => L (f p)) (x, t) =
      L (spatialDerivativeWord vs f (x, t)) := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : (fun z => spatialDerivativeWord vs (fun p => L (f p)) (z, t)) =ᶠ[𝓝 x]
        (fun z => L (spatialDerivativeWord vs f (z, t))) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact ih hz
    have hd := ((spatialDerivativeWord_smooth_slice hS hf vs).contDiffAt
      (hS.mem_nhds hx)).differentiableAt (by simp)
    have hc : HasFDerivAt (fun z => L (spatialDerivativeWord vs f (z, t)))
        (L.comp (fderiv ℝ (fun z => spatialDerivativeWord vs f (z, t)) x)) x := by
      convert! L.hasFDerivAt.comp x hd.hasFDerivAt using 1
    change fderiv ℝ (fun z => spatialDerivativeWord vs (fun p => L (f p)) (z, t)) x v = _
    rw [he.fderiv_eq, hc.fderiv]
    rfl

end Yau.NodeProofs.F01Aux
