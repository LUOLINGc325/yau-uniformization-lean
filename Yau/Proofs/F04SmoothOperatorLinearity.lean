import Yau.Proofs.F04ClosedParabolicGradient
import Yau.LeafProofs.L16

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- The actual second spatial differential is additive at a twice smooth
 point. The first-differential equality is proved on a genuine neighborhood
 before differentiating it. -/
theorem secondFDeriv_add_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact fderiv_fun_add (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  exact heq.fderiv_eq.trans (fderiv_fun_add hfd hgd)

/-- On the interior of either time set, changing the spatial cylinder or
 its time face changes no actual pointwise operator. -/
theorem linearOp_product_time_eq
    {n : ℕ} {O V : Set (Space n)} {I J : Set ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {u : Point n → ℝ}
    {p : Point n} (hO : p.1 ∈ O) (hV : p.1 ∈ V)
    (hI : I ∈ 𝓝 p.2) (hJ : J ∈ 𝓝 p.2) :
    linearOp (O ×ˢ I) a b u p = linearOp (V ×ˢ J) a b u p := by
  have hfO : {t : ℝ | (p.1,t) ∈ O ×ˢ I} = I := by ext t; simp [hO]
  have hfV : {t : ℝ | (p.1,t) ∈ V ×ˢ J} = J := by ext t; simp [hV]
  simp only [linearOp, timeD, hfO, hfV,
    derivWithin_of_mem_nhds hI, derivWithin_of_mem_nhds hJ]

/-- The actual nondivergence operator is additive for genuinely jointly
 smooth functions on an open product. No C2 certificate is an input. -/
theorem linearOp_add_of_smooth
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ} (hO : IsOpen O) (hI : IsOpen I)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {u v : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) (hv : ContDiffOn ℝ ∞ v (O ×ˢ I))
    {p : Point n} (hp : p ∈ O ×ˢ I) :
    linearOp (O ×ˢ I) a b (fun q => u q + v q) p =
      linearOp (O ×ˢ I) a b u p + linearOp (O ×ˢ I) a b v p := by
  have hUs : ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1 :=
    (((hu.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x hx => ⟨hx,hp.2⟩)).contDiffAt (hO.mem_nhds hp.1)).of_le (by norm_num))
  have hVs : ContDiffAt ℝ 2 (fun x => v (x,p.2)) p.1 :=
    (((hv.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x hx => ⟨hx,hp.2⟩)).contDiffAt (hO.mem_nhds hp.1)).of_le (by norm_num))
  have hUt : DifferentiableAt ℝ (fun t => u (p.1,t)) p.2 :=
    ((hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun t ht => ⟨hp.1,ht⟩)).contDiffAt (hI.mem_nhds hp.2)).differentiableAt (by simp)
  have hVt : DifferentiableAt ℝ (fun t => v (p.1,t)) p.2 :=
    ((hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun t ht => ⟨hp.1,ht⟩)).contDiffAt (hI.mem_nhds hp.2)).differentiableAt (by simp)
  have hD : spatialD (fun q => u q + v q) p = spatialD u p + spatialD v p :=
    fderiv_fun_add (hUs.differentiableAt (by norm_num)) (hVs.differentiableAt (by norm_num))
  have hDD : spatialDD (fun q => u q + v q) p = spatialDD u p + spatialDD v p :=
    secondFDeriv_add_of_contDiffAt hUs hVs
  have hT : timeD (O ×ˢ I) (fun q => u q + v q) p =
      timeD (O ×ˢ I) u p + timeD (O ×ˢ I) v p :=
    derivWithin_fun_add hUt.differentiableWithinAt hVt.differentiableWithinAt
  simp only [linearOp, hD, hDD, hT, add_apply, mul_add, Finset.sum_add_distrib]
  ring

end Yau.F04Proof
