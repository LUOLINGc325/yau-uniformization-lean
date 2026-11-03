import Yau.LeafProofs.L05ABPClosure

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem viscosity_abp_closed {n : ℕ} {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L) {v g : Point n → ℝ}
    (hv : ContinuousOn v (unitClosed n)) (hg : ContinuousOn g (unitClosed n))
    (hboundary : ∀ z∈parabolicBoundary n, v z≤0)
    (hsub : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) g v)
    {p : Point n} (hp : p∈unitClosed n) :
    v p≤abpC n ell*(∫ z in unitOpen n, (max (g z) 0)^(2*n+1))^(1/((2*n+1 : ℕ):ℝ)) := by
  let r : ℕ → ℝ := fun j => (1/((j:ℝ)+1))/4
  have hr (j : ℕ) : 0<r j := by dsimp only [r]; positivity
  have hr1 (j : ℕ) : r j≤1/4 := by
    have hh : (1:ℝ)/((j:ℝ)+1)≤1 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+1)).mpr
      norm_num
    dsimp only [r]
    linarith
  have hr0 : Tendsto r atTop (𝓝 0) := by
    simpa only [r,zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4
  let q : ℕ → Point n := fun j => ((1-r j) • p.1,(1-2*r j)*p.2-r j)
  have hq (j : ℕ) : q j∈unitOpen n := by
    have hx : ‖p.1‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    have hr' : 0<1-r j := by linarith [hr1 j]
    have hc : 0≤1-2*r j := by linarith [hr1 j]
    have hnorm : ‖(q j).1‖<1 := by
      dsimp only [q]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr']
      have hh := mul_le_mul_of_nonneg_left hx hr'.le
      linarith [hr j]
    have htime0 := mul_le_mul_of_nonneg_left hp.2.1 hc
    have htime1 := mul_le_mul_of_nonneg_left hp.2.2 hc
    refine ⟨?_,?_,?_⟩
    · simpa only [Metric.mem_ball,dist_zero_right] using hnorm
    · dsimp only [q]
      linarith [hr j]
    · dsimp only [q]
      linarith [hr j]
  have hqt : Tendsto q atTop (𝓝 p) := by
    have hx := ((tendsto_const_nhds (x := (1:ℝ))).sub hr0).smul (tendsto_const_nhds (x := p.1))
    have ht := (((tendsto_const_nhds (x := (1:ℝ))).sub (hr0.const_mul 2)).mul
      (tendsto_const_nhds (x := p.2))).sub hr0
    have hh := hx.prodMk_nhds ht
    simpa only [q,sub_zero,mul_zero,one_mul,one_smul,Prod.eta] using hh
  have hqtD : Tendsto q atTop (𝓝[unitClosed n] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqt,Filter.Eventually.of_forall (fun j => unitOpen_subset_unitClosed (hq j))⟩
  apply le_of_tendsto ((hv p hp).tendsto.comp hqtD)
  exact Filter.Eventually.of_forall (fun j => viscosity_abp_interior hell hL hv hg hboundary hsub (hq j))

/-- The original Pucci parabolic ABP tracking boundary, discharged internally. -/
theorem parabolicContactABPGap_proved : ParabolicContactABPGap := by
  intro n _hn ell L hell hL
  refine ⟨abpC n ell,abpC_pos n hell,?_⟩
  intro v g hv hg hboundary hsub p hp
  have hh := viscosity_abp_closed hell hL hv hg hboundary hsub hp
  rw [productVolume_eq_restrict]
  exact hh

end Yau.LeafProofs.L05Aux
