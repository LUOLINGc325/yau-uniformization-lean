import Yau.LeafProofs.L05PerturbationTaylorBasic

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_time_taylor_remainder {n : ℕ} {sigma C r : ℝ}
    (hs : 0 < sigma) {u : Point n → ℝ} (hh : SchauderBound sigma (backward (1/4)) u C)
    (hr : 0 < r) (hrb : r ≤ 1/8) {p : Point n} (hp : p∈perturbClosed (0 : Space n) r 0) :
    |u p-u (p.1,0)-timeD (backward (1/4)) u 0*p.2| ≤ 2*C*r^sigma*r^2 := by
  let q := timeD (backward (1/4)) u (0 : Point n)
  let g : ℝ → ℝ := fun t => u (p.1,t)-q*t
  have hpB := perturb_small_closed_subset_quarter hr hrb hp
  have hSlice : {t : ℝ | (p.1,t)∈backward (1/4)}=Ioc (-(1/4 : ℝ)^2) 0 := by
    ext t
    simp only [backward,mem_prod,hpB.1,true_and,mem_setOf_eq]
  have hSub : Icc p.2 0 ⊆ Ioc (-(1/4 : ℝ)^2) 0 :=
    fun _ ht => ⟨hpB.2.1.trans_le ht.1,ht.2⟩
  have hPoint (s : ℝ) (hst : s∈Icc p.2 0) : (p.1,s)∈perturbClosed (0 : Space n) r 0 :=
    ⟨hp.1,hp.2.1.trans hst.1,hst.2⟩
  have hDeriv (s : ℝ) (hst : s∈Icc p.2 0) :
      HasDerivWithinAt g (timeD (backward (1/4)) u (p.1,s)-q) (Icc p.2 0) s := by
    have hps := perturb_small_closed_subset_quarter hr hrb (hPoint s hst)
    have hd := (hh.1.2.2.2.2.2 (p.1,s) hps).hasDerivWithinAt
    change HasDerivWithinAt (fun t => u (p.1,t)) (timeD (backward (1/4)) u (p.1,s))
      {t : ℝ | (p.1,t)∈backward (1/4)} s at hd
    rw [hSlice] at hd
    have hqD : HasDerivWithinAt (fun t : ℝ => q*t) q (Icc p.2 0) s := by
      simpa only [id_eq,mul_one] using (((hasDerivAt_id s).const_mul q).hasDerivWithinAt (s := Icc p.2 0))
    exact (hd.mono hSub).sub hqD
  have hBound (s : ℝ) (hst : s∈Icc p.2 0) :
      ‖timeD (backward (1/4)) u (p.1,s)-q‖ ≤ 2*C*r^sigma :=
    perturb_time_holder_at_zero hs hh hr hrb (hPoint s hst)
  have hMean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hDeriv hBound
    (convex_Icc p.2 0) (left_mem_Icc.mpr hp.2.2) (right_mem_Icc.mpr hp.2.2)
  rw [Real.norm_eq_abs,abs_sub_comm (g 0) (g p.2)] at hMean
  have hExpr : g p.2-g 0=u p-u (p.1,0)-q*p.2 := by
    dsimp only [g]
    change u p-q*p.2-(u (p.1,0)-q*0)=u p-u (p.1,0)-q*p.2
    ring
  rw [hExpr] at hMean
  simp only [Real.norm_eq_abs,zero_sub,abs_neg] at hMean
  have hTime : |p.2| ≤ r^2 := by
    rw [abs_of_nonpos hp.2.2]
    have hlo : -r^2 ≤ p.2 := by simpa only [zero_sub] using hp.2.1
    linarith
  exact hMean.trans (mul_le_mul_of_nonneg_left hTime
    (mul_nonneg (mul_nonneg (by norm_num) hh.2.1) (Real.rpow_nonneg hr.le sigma)))

end Yau.LeafProofs.L05Aux
