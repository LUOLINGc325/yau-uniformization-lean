import Yau.LeafProofs.L16InteriorMaximum

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Linearity of the actual operator needs derivatives only at its evaluation point. -/
theorem linearOp_sub_at {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {u v : Point n → ℝ} {p : Point n}
    (hu : ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1)
    (hv : ContDiffAt ℝ 2 (fun x => v (x,p.2)) p.1)
    (hut : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) {t | (p.1,t) ∈ Q} p.2)
    (hvt : DifferentiableWithinAt ℝ (fun t => v (p.1,t)) {t | (p.1,t) ∈ Q} p.2) :
    linearOp Q a b (fun z => u z - v z) p = linearOp Q a b u p - linearOp Q a b v p := by
  have hD : spatialD (fun z => u z-v z) p = spatialD u p-spatialD v p :=
    fderiv_fun_sub (hu.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num))
  have hDD : spatialDD (fun z => u z-v z) p = spatialDD u p-spatialDD v p :=
    L16Aux.secondFDeriv_sub hu hv
  have ht : timeD Q (fun z => u z-v z) p = timeD Q u p-timeD Q v p :=
    derivWithin_fun_sub hut hvt
  simp only [linearOp, hD, hDD, ht, ContinuousLinearMap.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  ring

theorem linearOp_neg {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (u : Point n → ℝ) (p : Point n) :
    linearOp Q a b (fun z => -u z) p = -linearOp Q a b u p := by
  have hD : spatialD (fun z => -u z) p = -spatialD u p := fderiv_fun_neg
  have hDD : spatialDD (fun z => -u z) p = -spatialDD u p := by
    simp only [spatialDD, fderiv_fun_neg]
  have ht : timeD Q (fun z => -u z) p = -timeD Q u p := derivWithin.neg
  simp only [linearOp, hD, hDD, ht, ContinuousLinearMap.neg_apply, mul_neg,
    Finset.sum_neg_distrib]
  ring

/-- The closed and half-open time slabs have the same derivative germ at every
positive time, including the terminal face. -/
theorem timeD_closed_eq_halfOpen {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {p : Point n} (hp : p ∈ O ×ˢ Ioc 0 T) (u : Point n → ℝ) :
    timeD (cylinder (closure O) 0 T) u p = timeD (O ×ˢ Ioc 0 T) u p := by
  have hc : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Icc 0 T := by
    ext t
    simp [cylinder, subset_closure hp.1]
  have ho : {t | (p.1,t) ∈ O ×ˢ Ioc 0 T} = Ioc 0 T := by
    ext t
    simp [hp.1]
  simp only [timeD, hc, ho]
  apply derivWithin_congr_set
  filter_upwards [Ioi_mem_nhds hp.2.1] with t ht
  simp only [mem_Icc, mem_Ioc]
  exact propext ⟨fun h => ⟨ht,h.2⟩, fun h => ⟨h.1.le,h.2⟩⟩

theorem d_log {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) (i : Yau.RIdx n) :
    d (fun y => Real.log (f y)) x i = d f x i / f x := by
  simp only [d, fderiv.log hf hx, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem d_mul {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Yau.RIdx n) :
    d (fun y => f y*g y) x i = d f x i*g x+f x*d g x i := by
  simp only [d, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem d_sum {n : ℕ} {ι : Type*} [Fintype ι]
    {f : ι → Space n → ℝ} {x : Space n}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Yau.RIdx n) :
    d (fun y => ∑ j, f j y) x i = ∑ j, d (f j) x i := by
  simp only [d, fderiv_fun_sum (fun j _ => hf j), ContinuousLinearMap.sum_apply]

theorem d_d {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (i j : Yau.RIdx n) :
    d (fun y => d f y j) x i = fderiv ℝ (fderiv ℝ f) x (Yau.realVec i) (Yau.realVec j) := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simpa only [d, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    congrArg (fun L : Space n →L[ℝ] ℝ => L (Yau.realVec i))
      (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Yau.realVec j) x)).fderiv

end Yau.LeafProofs.L16ExpBoundaryAux
