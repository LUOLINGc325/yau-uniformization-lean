import Yau.LeafProofs.L05PerronCalculus

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perron_truncation_subset {n : ℕ} {s : ℝ} (hs : s < 1) :
    abpClosed n 1 (-1) s⊆perronSlab n :=
  fun _ hp => ⟨hp.1,hp.2.1,hp.2.2.trans_lt hs⟩

theorem perron_truncatedBoundary_subset {n : ℕ} {s : ℝ} (hs : s < 1) :
    abpBoundary n 1 (-1) s⊆perronBoundary n := by
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr ⟨hp.1,hp.2.1,hp.2.2.trans_lt hs⟩

theorem perron_truncatedBoundary_compact (n : ℕ) (s : ℝ) :
    IsCompact (abpBoundary n 1 (-1) s) :=
  ((isCompact_closedBall (0 : Space n) 1).prod isCompact_singleton).union
    ((isCompact_sphere (0 : Space n) 1).prod isCompact_Icc)

theorem perron_truncatedBoundary_closed {n : ℕ} {s : ℝ} (hs : -1 ≤ s) :
    abpBoundary n 1 (-1) s⊆abpClosed n 1 (-1) s := by
  intro p hp
  rcases hp with hp | hp
  · exact ⟨hp.1,by rw [show p.2=(-1:ℝ) from hp.2]; exact ⟨le_rfl,hs⟩⟩
  · exact ⟨Metric.sphere_subset_closedBall hp.1,hp.2⟩

theorem perron_buffer_subset_truncation {n : ℕ} {delta b s : ℝ}
    (hd : 0 ≤ delta) (hbs : b ≤ s) :
    abpClosed n (1-delta) (-1+delta) b⊆abpClosed n 1 (-1) s := by
  intro z hz
  have hnorm : ‖z.1‖ ≤ 1-delta := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
  refine ⟨?_,?_,hz.2.2.trans hbs⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖z.1‖ ≤ 1 by linarith)
  · linarith [hz.2.1]

theorem perron_buffer_optimizer_interior {n : ℕ} {delta b s d : ℝ}
    (hd : 0 < delta) (hbs : b < s) (hs : s < 1) (hdd : d ≤ delta/2) (hdt : d ≤ (s-b)/2)
    {z q : Point n} (hz : z∈abpClosed n (1-delta) (-1+delta) b) (hnear : dist q z < d) :
    q∈interior (abpClosed n 1 (-1) s) ∧ q∈perronOpen n := by
  have hnorm : ‖z.1‖ ≤ 1-delta := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
  have hdx : ‖q.1-z.1‖ ≤ dist q z := by
    simpa only [dist_eq_norm,Prod.fst_sub] using norm_fst_le (q-z)
  have htime : |q.2-z.2| ≤ dist q z := by
    simpa only [dist_eq_norm,Prod.snd_sub,Real.norm_eq_abs] using norm_snd_le (q-z)
  have htri : ‖q.1‖ ≤ ‖q.1-z.1‖+‖z.1‖ := by
    simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub q.1 z.1 (0 : Space n)
  have hqx : q.1∈Metric.ball (0 : Space n) 1 := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith
  have hqa : -1 < q.2 := by linarith [(abs_le.mp htime).1,hz.2.1]
  have hqs : q.2 < s := by linarith [(abs_le.mp htime).2,hz.2.2]
  refine ⟨?_,hqx,hqa,hqs.trans hs⟩
  apply mem_interior_iff_mem_nhds.mpr
  have hnb : (Metric.ball (0 : Space n) 1 ×ˢ Set.Ioo (-1) s)∈𝓝 q :=
    (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hqx,hqa,hqs⟩
  apply mem_of_superset hnb
  intro p hp
  exact ⟨Metric.ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2.le⟩

theorem perron_buffer_boundary_near {n : ℕ} {delta b s : ℝ}
    (hd : 0 < delta) (hd1 : delta < 1/2) (hab : -1+delta ≤ b) (hbs : b ≤ s)
    {z : Point n} (hz : z∈abpBoundary n (1-delta) (-1+delta) b) :
    ∃ p∈abpBoundary n 1 (-1) s, dist z p ≤ delta := by
  have hR : 0 < 1-delta := by linarith
  rcases hz with hz | hz
  · have ht : z.2=-1+delta := hz.2
    have hx : ‖z.1‖ ≤ 1-delta := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
    refine ⟨(z.1,-1),Or.inl ⟨?_,rfl⟩,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖z.1‖ ≤ 1 by linarith)
    · rw [dist_eq_norm]
      simp only [Prod.sub_def,sub_self,Prod.norm_mk,norm_zero,Real.norm_eq_abs,ht]
      rw [show -1+delta-(-1)=delta by ring,abs_of_pos hd,max_eq_right hd.le]
  · have hx : ‖z.1‖=1-delta := by simpa only [Metric.mem_sphere,dist_zero_right] using hz.1
    let p : Point n := ((1-delta)⁻¹ • z.1,z.2)
    have hpx : ‖p.1‖=1 := by
      dsimp only [p]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),hx,inv_mul_cancel₀ hR.ne']
    have hpt : p.2∈Set.Icc (-1:ℝ) s := ⟨by change -1 ≤ z.2; linarith [hz.2.1],hz.2.2.trans hbs⟩
    refine ⟨p,Or.inr ⟨?_,hpt⟩,?_⟩
    · simpa only [Metric.mem_sphere,dist_zero_right] using hpx
    · rw [dist_eq_norm]
      have he : z-p=((1-(1-delta)⁻¹) • z.1,0) := by
        apply Prod.ext
        · change z.1-(1-delta)⁻¹ • z.1=(1-(1-delta)⁻¹) • z.1
          module
        · exact sub_self _
      rw [he,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _),norm_smul,Real.norm_eq_abs,hx]
      have hcoef : 1-(1-delta)⁻¹= -delta/(1-delta) := by field_simp; ring
      rw [hcoef,abs_div,abs_neg,abs_of_pos hd,abs_of_pos hR,div_mul_cancel₀ _ hR.ne']

end Yau.LeafProofs.L05Aux
