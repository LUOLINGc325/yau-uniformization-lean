import Yau.Proofs.F05ExponentialTransform

/-! The exact exponential divergence transform on an actual open physical
patch, including its one-sided terminal face. No data on a spherical rim. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryAux

theorem F05_timeD_exp_open {n : ℕ} {O : Set (Space n)} {T : ℝ} (hT : 0 < T)
    {w : Point n → ℝ} (hw : ContDiffOn ℝ ∞ w (O ×ˢ Ioc 0 T))
    {p : Point n} (hp : p ∈ O ×ˢ Ioc 0 T) :
    timeD (O ×ˢ Ioc 0 T) (fun q => Real.exp (w q)) p =
      Real.exp (w p)*timeD (O ×ˢ Ioc 0 T) w p := by
  have hFiber : {r | (p.1,r) ∈ O ×ˢ Ioc 0 T} = Ioc 0 T := by
    ext r
    simp only [mem_ofPred_eq,mem_prod,hp.1,true_and]
  have hSlice : ContDiffOn ℝ ∞ (fun t => w (p.1,t)) (Ioc 0 T) :=
    hw.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun t ht => ⟨hp.1,ht⟩)
  have hDiff := hSlice.differentiableOn (by simp) p.2 hp.2
  have hTime : HasDerivWithinAt (fun t => w (p.1,t))
      (timeD (O ×ˢ Ioc 0 T) w p) (Ioc 0 T) p.2 := by
    simpa only [timeD,hFiber] using hDiff.hasDerivWithinAt
  have hExp := hTime.exp.derivWithin (uniqueDiffOn_Ioc (0 : ℝ) T p.2 hp.2)
  simpa only [timeD,hFiber,Prod.eta] using hExp

theorem F05_exp_divergence_equation_open {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {T : ℝ} (hT : 0 < T) {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {R w : Point n → ℝ} (ha : ContDiffOn ℝ ∞ a (O ×ˢ Ioc 0 T))
    (hw : ContDiffOn ℝ ∞ w (O ×ˢ Ioc 0 T))
    (hEquation : ∀ p ∈ O ×ˢ Ioc 0 T,
      linearOp (O ×ˢ Ioc 0 T) (fun q => Real.exp (-w q) • a q)
        (fun q j => Real.exp (-w q)*b q j) w p = (1-Real.exp (-w p))*R p) :
    ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R (fun q => Real.exp (w q)) := by
  intro p hp
  have hSpatial (x : Space n) (hx : x ∈ O) : ContDiffAt ℝ 2 (fun y => w (y,p.2)) x := by
    have hSlice := hw.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (show MapsTo (fun y : Space n => (y,p.2)) O (O ×ˢ Ioc 0 T) from fun y hy => ⟨hy,hp.2⟩)
    exact (hSlice.contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have hSlice : ContDiffOn ℝ ∞ (fun x => a (x,p.2)) O :=
    ha.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => ⟨hx,hp.2⟩)
  have had (i j : Yau.RIdx n) : DifferentiableAt ℝ (fun x => a (x,p.2) i j) p.1 :=
    (matrixEntryCLM i j).differentiableAt.comp p.1
      ((hSlice.contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp))
  have hFlux := F05_exp_flux_divergence hO hp.1 had hSpatial
  have hGrad (j : Yau.RIdx n) : d (fun x => Real.exp (w (x,p.2))) p.1 j =
      Real.exp (w p)*spatialD w p (Yau.realVec j) := by
    simp only [d,fderiv_exp ((hSpatial p.1 hp.1).differentiableAt (by norm_num)),
      ContinuousLinearMap.smul_apply,smul_eq_mul,Prod.eta]
    rfl
  let H := ∑ i,∑ j,a p i j*spatialDD w p (Yau.realVec i) (Yau.realVec j)
  let D := ∑ j,b p j*spatialD w p (Yau.realVec j)
  let G := ∑ i,∑ j,d (fun x => a (x,p.2) i j) p.1 i*spatialD w p (Yau.realVec j)
  have hDiv : (∑ i,d (fun x => ∑ j,(a (x,p.2) i j/Real.exp (w (x,p.2)))*
      d (fun y => Real.exp (w (y,p.2))) x j) p.1 i) = G+H := by
    simp only [hFlux,Finset.sum_add_distrib]
    rfl
  have hDrift : (∑ j,(b p j-∑ i,d (fun x => a (x,p.2) i j) p.1 i)/Real.exp (w p)*
      d (fun x => Real.exp (w (x,p.2))) p.1 j) = D-G := by
    simp only [hGrad]
    have hEach (j : Yau.RIdx n) :
        (b p j-∑ i,d (fun x => a (x,p.2) i j) p.1 i)/Real.exp (w p)*
          (Real.exp (w p)*spatialD w p (Yau.realVec j)) =
        b p j*spatialD w p (Yau.realVec j)-
          ∑ i,d (fun x => a (x,p.2) i j) p.1 i*spatialD w p (Yau.realVec j) := by
      rw [← Finset.sum_mul]
      field_simp [Real.exp_ne_zero]
    simp only [hEach,Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  have hSumA : (∑ i,∑ j,(Real.exp (-w p) • a p) i j*spatialDD w p (Yau.realVec i) (Yau.realVec j)) =
      Real.exp (-w p)*H := by
    simp only [H,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  have hSumB : (∑ j,Real.exp (-w p)*b p j*spatialD w p (Yau.realVec j)) = Real.exp (-w p)*D := by
    simp only [D,Finset.mul_sum,mul_assoc]
  have hEq := hEquation p hp
  unfold linearOp at hEq
  rw [hSumA,hSumB] at hEq
  have hInverse : Real.exp (w p)*Real.exp (-w p) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hScaled := congrArg (fun x : ℝ => Real.exp (w p)*x) hEq
  have hMain : Real.exp (w p)*timeD (O ×ˢ Ioc 0 T) w p-H-D = (Real.exp (w p)-1)*R p := by
    linear_combination hScaled+(H+D-R p)*hInverse
  rw [F05_timeD_exp_open hT hw hp,hDiv,hDrift]
  linarith

end Yau.Proofs.F05Aux
