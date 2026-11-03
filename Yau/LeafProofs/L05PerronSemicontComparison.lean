import Yau.LeafProofs.L05PerronComparison
import Yau.LeafProofs.L05PerronCollar
import Yau.LeafProofs.L05PerronGeometry

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

set_option maxHeartbeats 1600000 in
theorem perron_semicont_compare {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) {u v : Point n → ℝ}
    (hu : UpperSemicontinuousOn u (perronSlab n))
    (hv : LowerSemicontinuousOn v (perronSlab n))
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ perronSlab n, |u p| ≤ M ∧ |v p| ≤ M)
    (hsub : viscositySub (perronOpen n) (fun H _ => F H) (fun _ => 0) u)
    (hsuper : viscositySuper (perronOpen n) (fun H _ => F H) (fun _ => 0) v)
    (hboundary : ∀ p ∈ perronBoundary n, u p ≤ v p) :
    ∀ p ∈ perronSlab n, u p ≤ v p := by
  obtain ⟨M,hM,hbound⟩ := hb
  let M1 := M+1
  have hM1 : 0 < M1 := by dsimp only [M1]; linarith
  have hinterior (p : Point n) (hp : p ∈ perronOpen n) : u p ≤ v p := by
    apply le_of_forall_pos_le_add
    intro eta heta
    obtain ⟨b,hpb,hb1⟩ := exists_between hp.2.2
    obtain ⟨s,hbs,hs1⟩ := exists_between hb1
    let K := abpClosed n 1 (-1) s
    let Gamma := abpBoundary n 1 (-1) s
    have hK : IsCompact K := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
    have hKC : K ⊆ perronSlab n := perron_truncation_subset hs1
    have hpK : p ∈ K := ⟨Metric.ball_subset_closedBall hp.1,hp.2.1.le,(hpb.trans hbs).le⟩
    have hne : K.Nonempty := ⟨p,hpK⟩
    have huK : UpperSemicontinuousOn u K := hu.mono hKC
    have hvK : LowerSemicontinuousOn v K := hv.mono hKC
    have hs : -1 ≤ s := (hp.2.1.trans (hpb.trans hbs)).le
    obtain ⟨rho,hrho,hcollar⟩ := perron_two_point_collar (perron_truncatedBoundary_compact n s)
      (perron_truncatedBoundary_closed hs) huK hvK
      (fun q hq => hboundary q (perron_truncatedBoundary_subset hs1 hq)) heta
    have hpx : 0 < 1-‖p.1‖ := by
      have hh : ‖p.1‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
      linarith
    have hpa : 0 < p.2+1 := by linarith [hp.2.1]
    obtain ⟨delta,hd,hdelta⟩ := exists_between
      (show 0 < min (1/2) (min (1-‖p.1‖) (min (p.2+1) (rho/4))) by positivity)
    have hds : delta < 1/2 ∧ delta < 1-‖p.1‖ ∧ delta < p.2+1 ∧ delta < rho/4 := by
      simpa only [lt_min_iff] using hdelta
    let D := abpClosed n (1-delta) (-1+delta) b
    let O := abpOpen n (1-delta) (-1+delta) b
    have hDK : D ⊆ K := perron_buffer_subset_truncation hd.le hbs.le
    have hOD : O ⊆ D :=
      fun q hq => ⟨Metric.ball_subset_closedBall hq.1,hq.2.1.le,hq.2.2.le⟩
    have hpD : p ∈ D := by
      refine ⟨?_,?_,hpb.le⟩
      · simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖p.1‖ ≤ 1-delta by linarith [hds.2.1])
      · linarith [hds.2.2.1]
    let d := min (delta/2) (min ((s-b)/2) (rho/4))
    have hdpos : 0 < d := by dsimp only [d]; positivity
    have hdd : d ≤ delta/2 := min_le_left _ _
    have hdt : d ≤ (s-b)/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hdr : d ≤ rho/4 := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨eps,heps,hes⟩ := exists_between (show 0 < d^2/(4*M1) by positivity)
    have hepsmall : 4*M1*eps < d^2 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 4*M1)).mp hes
      nlinarith
    have hbu : ∀ q ∈ K, |u q| ≤ M1 := by
      intro q hq
      have hh := (hbound q (hKC hq)).1
      dsimp only [M1]
      linarith
    have hbv : ∀ q ∈ K, |v q| ≤ M1 := by
      intro q hq
      have hh := (hbound q (hKC hq)).2
      dsimp only [M1]
      linarith
    let S := perronSupConv K eps u
    let I := perronInfConv K eps v
    have hnearS (z : Point n) (hz : z ∈ D) (q : Point n) (hq : q ∈ K)
        (ha : S z=u q-qnorm2 (z-q)/(2*eps)) : dist q z < d := by
      have hc := perron_supConv_displacement hne hK huK hbu heps (hDK hz) hq ha
      have hh := norm_sq_le_qnorm2 (z-q)
      rw [dist_comm q z,dist_eq_norm]
      nlinarith [norm_nonneg (z-q)]
    have hnearI (z : Point n) (hz : z ∈ D) (q : Point n) (hq : q ∈ K)
        (ha : I z=v q+qnorm2 (z-q)/(2*eps)) : dist q z < d := by
      have hc := perron_infConv_displacement hne hK hvK hbv heps (hDK hz) hq ha
      have hh := norm_sq_le_qnorm2 (z-q)
      rw [dist_comm q z,dist_eq_norm]
      nlinarith [norm_nonneg (z-q)]
    have hSsub : viscositySub O (fun H _ => F H) (fun _ => 0) S := by
      intro z hz phi hphi ht
      obtain ⟨q,hq,ha⟩ := perron_supConv_attained hne hK huK eps z
      obtain ⟨hqK,hqO⟩ := perron_buffer_optimizer_interior hd hbs hs1 hdd hdt
        (hOD hz) (hnearS z (hOD hz) q hq ha)
      exact perron_supConv_viscosity_jet hne hK huK eps hsub hqK hqO ha hphi ht
    have hIsuper : viscositySuper O (fun H _ => F H) (fun _ => 0) I := by
      intro z hz phi hphi ht
      obtain ⟨q,hq,ha⟩ := perron_infConv_attained hne hK hvK eps z
      obtain ⟨hqK,hqO⟩ := perron_buffer_optimizer_interior hd hbs hs1 hdd hdt
        (hOD hz) (hnearI z (hOD hz) q hq ha)
      exact perron_infConv_viscosity_jet hne hK hvK eps hsuper hqK hqO ha hphi ht
    have hab : -1+delta < b := by linarith [hds.2.2.1,hpb]
    have hbd : ∀ z ∈ abpBoundary n (1-delta) (-1+delta) b, S z ≤ I z+eta := by
      intro z hz
      have hzD : z ∈ D := by
        rcases hz with hz | hz
        · exact ⟨hz.1,by rw [show z.2= -1+delta from hz.2]; exact ⟨le_rfl,hab.le⟩⟩
        · exact ⟨Metric.sphere_subset_closedBall hz.1,hz.2⟩
      obtain ⟨xi,hxi,hdist⟩ := perron_buffer_boundary_near hd hds.1 hab.le hbs.le hz
      obtain ⟨q,hq,haq⟩ := perron_supConv_attained hne hK huK eps z
      obtain ⟨r,hr,har⟩ := perron_infConv_attained hne hK hvK eps z
      have hqxi : dist q xi < rho := by
        have hh := dist_triangle q z xi
        linarith [hnearS z hzD q hq haq,hds.2.2.2]
      have hrxi : dist r xi < rho := by
        have hh := dist_triangle r z xi
        linarith [hnearI z hzD r hr har,hds.2.2.2]
      have hvalue := hcollar xi hxi q hq r hr hqxi hrxi
      have hSle : S z ≤ u q := by
        dsimp only [S]
        rw [haq]
        exact sub_le_self _ (div_nonneg (qnorm2_nonneg _) (by positivity))
      have hIge : v r ≤ I z := by
        dsimp only [I]
        rw [har]
        exact le_add_of_nonneg_right (div_nonneg (qnorm2_nonneg _) (by positivity))
      calc
        _ ≤ u q := hSle
        _ ≤ v r+eta := by linarith
        _ ≤ I z+eta := add_le_add hIge le_rfl
    have hcompare := perron_continuous_compare hn hell hL (show 0 < 1-delta by linarith [hds.1]) hab
      hF hE (perron_supConv_continuous hne hK huK eps).continuousOn
      (perron_infConv_continuous hne hK hvK eps).continuousOn hSsub hIsuper hbd p hpD
    have hdiagS := perron_supConv_diagonal hne hK huK eps hpK
    have hdiagI := perron_infConv_diagonal hne hK hvK eps hpK
    linarith
  intro p hp
  by_cases hx : p.1 ∈ Metric.ball (0 : Space n) 1
  · by_cases ht : -1 < p.2
    · exact hinterior p ⟨hx,ht,hp.2.2⟩
    · have hpt : p.2= -1 := le_antisymm (le_of_not_gt ht) hp.2.1
      exact hboundary p (Or.inl ⟨hp.1,hpt⟩)
  · have hpn : ‖p.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    have hpn' : ¬‖p.1‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hpeq : ‖p.1‖=1 := le_antisymm hpn (le_of_not_gt hpn')
    exact hboundary p (Or.inr ⟨by simpa only [Metric.mem_sphere,dist_zero_right] using hpeq,hp.2⟩)

end Yau.LeafProofs.L05Aux
