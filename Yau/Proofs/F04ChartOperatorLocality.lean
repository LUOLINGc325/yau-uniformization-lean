import Yau.Proofs.F04PhysicalChartOperator
import Yau.LeafProofs.L16

open Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic

/-- Equality on an open spatial product preserves the actual operator
 on ANY time set, including closed one-sided time faces. -/
theorem linearOp_congr_product_of_eqOn
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {I : Set ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {u v : Point n → ℝ}
    (he : EqOn u v (O ×ˢ I)) {p : Point n} (hp : p ∈ O ×ˢ I) :
    linearOp (O ×ˢ I) a b u p = linearOp (O ×ˢ I) a b v p := by
  have hs : (fun x => u (x,p.2)) =ᶠ[𝓝 p.1] (fun x => v (x,p.2)) :=
    eventually_of_mem (hO.mem_nhds hp.1) (fun x hx => he ⟨hx,hp.2⟩)
  have hD : spatialD u p = spatialD v p := hs.fderiv_eq
  have hDD : spatialDD u p = spatialDD v p := hs.fderiv.fderiv_eq
  have hT : timeD (O ×ˢ I) u p = timeD (O ×ˢ I) v p := by
    have hFiber : {t : ℝ | (p.1,t) ∈ O ×ˢ I} = I := by ext t; simp [hp.1]
    simp only [timeD,hFiber]
    exact derivWithin_congr (fun t ht => he ⟨hp.1,ht⟩) (he hp)
  simp only [linearOp,hD,hDD,hT]

/-- A genuine smooth local chart supplies the local C2 spatial germ of
 ANY function agreeing with it on the actual product. -/
theorem spatialSlice_C2_of_eqOn
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {I : Set ℝ}
    {u v : Point n → ℝ} (he : EqOn u v (O ×ˢ I))
    (hv : ContDiffOn ℝ ∞ v (O ×ˢ I)) {p : Point n} (hp : p ∈ O ×ˢ I) :
    ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1 := by
  have hs : (fun x => u (x,p.2)) =ᶠ[𝓝 p.1] (fun x => v (x,p.2)) :=
    eventually_of_mem (hO.mem_nhds hp.1) (fun x hx => he ⟨hx,hp.2⟩)
  have hvs : ContDiffOn ℝ ∞ (fun x => v (x,p.2)) O :=
    hv.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,hp.2⟩)
  exact ((hvs.contDiffAt (hO.mem_nhds hp.1)).of_le (by norm_num)).congr_of_eventuallyEq hs

end Yau.F04Proof
