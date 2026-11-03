import Yau.LeafProofs.L05PerronClassical

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perronMaxPatch {n : ℕ} (w z : Point n → ℝ) (p : Point n) (r : ℝ) (q : Point n) : ℝ :=
  if dist q p<r then max (w q) (z q) else w q

theorem perron_patch_outer_eq {n : ℕ} {w z : Point n → ℝ} {p q : Point n} {r : ℝ}
    (hcollar : ∀ x, r/2 ≤ dist x p → dist x p ≤ r → z x ≤ w x)
    (hq : r/2 ≤ dist q p) : perronMaxPatch w z p r q=w q := by
  unfold perronMaxPatch
  split_ifs with hq'
  · exact max_eq_left (hcollar q hq hq'.le)
  · rfl

theorem perron_patch_inner_eventually {n : ℕ} (w z : Point n → ℝ) (p : Point n) (r : ℝ)
    {q : Point n} (hq : dist q p<r) :
    perronMaxPatch w z p r =ᶠ[𝓝 q] (fun x => max (w x) (z x)) := by
  have hnear : Metric.ball p r∈𝓝 q := Metric.isOpen_ball.mem_nhds hq
  filter_upwards [hnear] with x hx
  exact if_pos hx

theorem perron_patch_outer_eventually {n : ℕ} {w z : Point n → ℝ} {p q : Point n} {r : ℝ}
    (hr : 0<r) (hcollar : ∀ x, r/2 ≤ dist x p → dist x p ≤ r → z x ≤ w x)
    (hq : r ≤ dist q p) : perronMaxPatch w z p r =ᶠ[𝓝 q] w := by
  have hq' : r/2<dist q p := by linarith
  have hopen : IsOpen {x : Point n | r/2<dist x p} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  filter_upwards [hopen.mem_nhds hq'] with x hx
  exact perron_patch_outer_eq hcollar hx.le

theorem perron_upperSemicont_eventuallyEq {n : ℕ} {C : Set (Point n)}
    {u v : Point n → ℝ} {p : Point n} (heq : u =ᶠ[𝓝 p] v)
    (hv : UpperSemicontinuousWithinAt v C p) : UpperSemicontinuousWithinAt u C p := by
  intro a ha
  have he : u p=v p := heq.eq_of_nhds
  have hva : v p<a := by linarith
  have hnear : ∀ᶠ q in 𝓝[C] p, v q<a := hv a hva
  have hEqC : ∀ᶠ q in 𝓝[C] p, u q=v q := heq.filter_mono nhdsWithin_le_nhds
  filter_upwards [hEqC,hnear] with q hq hqa
  change u q<a
  rw [hq]
  exact hqa

theorem perron_patch_usc {n : ℕ} {C : Set (Point n)} {w z : Point n → ℝ} {p : Point n} {r : ℝ}
    (hr : 0<r) (hw : UpperSemicontinuousOn w C)
    (hz : ContinuousOn z (Metric.closedBall p r))
    (hcollar : ∀ q, r/2 ≤ dist q p → dist q p ≤ r → z q ≤ w q) :
    UpperSemicontinuousOn (perronMaxPatch w z p r) C := by
  intro q hq
  by_cases hqin : dist q p<r
  · have hzc : ContinuousAt z q := (hz q (Metric.ball_subset_closedBall hqin)).continuousAt
      (Metric.closedBall_mem_nhds_of_mem hqin)
    apply perron_upperSemicont_eventuallyEq (perron_patch_inner_eventually w z p r hqin)
    convert! UpperSemicontinuousWithinAt.sup (hw q hq)
      hzc.continuousWithinAt.upperSemicontinuousWithinAt using 1
  · exact perron_upperSemicont_eventuallyEq
      (perron_patch_outer_eventually hr hcollar (le_of_not_gt hqin)) (hw q hq)

theorem perron_patch_sub {n : ℕ} {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    {g w z : Point n → ℝ} {p : Point n} {r : ℝ} (hr : 0<r)
    (hball : Metric.closedBall p r⊆Q) (hw : viscositySub Q G g w)
    (hz : viscositySub (Metric.ball p r) G g z)
    (hcollar : ∀ q, r/2 ≤ dist q p → dist q p ≤ r → z q ≤ w q) :
    viscositySub Q G g (perronMaxPatch w z p r) := by
  intro q hq phi hphi ht
  by_cases hqin : dist q p<r
  · have hwB := viscositySub_mono_domain hw (fun x hx => hball (Metric.ball_subset_closedBall hx))
    have hmax := viscositySub_max hwB hz
    exact hmax q hqin phi hphi
      (touchAbove_of_eventuallyEq (perron_patch_inner_eventually w z p r hqin) ht)
  · exact hw q hq phi hphi
      (touchAbove_of_eventuallyEq (perron_patch_outer_eventually hr hcollar (le_of_not_gt hqin)) ht)

theorem perron_patch_ge {n : ℕ} (w z : Point n → ℝ) (p : Point n) (r : ℝ) (q : Point n) :
    w q≤perronMaxPatch w z p r q := by
  unfold perronMaxPatch
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem perron_patch_bounds {n : ℕ} {C : Set (Point n)} {w z : Point n → ℝ}
    {p : Point n} {r B : ℝ} (hw : ∀ q∈C, -B≤w q ∧ w q≤B)
    (hz : ∀ q∈Metric.closedBall p r, z q<B) :
    ∀ q∈C, -B≤perronMaxPatch w z p r q ∧ perronMaxPatch w z p r q≤B := by
  intro q hq
  refine ⟨(hw q hq).1.trans (perron_patch_ge w z p r q),?_⟩
  unfold perronMaxPatch
  split_ifs with hqin
  · exact max_le (hw q hq).2 (hz q (Metric.ball_subset_closedBall hqin)).le
  · exact (hw q hq).2

theorem perron_boundary_not_open {n : ℕ} {p : Point n} (hp : p∈perronBoundary n) :
    p∉perronOpen n := by
  intro hq
  rcases hp with hp | hp
  · have hh : p.2=(-1:ℝ) := hp.2
    linarith [hq.2.1]
  · have hh : ‖p.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.1
    have hlt : ‖p.1‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hq.1
    linarith

theorem perron_patch_boundary_eq {n : ℕ} (w z : Point n → ℝ) {p : Point n} {r : ℝ}
    (hball : Metric.closedBall p r⊆perronOpen n) {q : Point n} (hq : q∈perronBoundary n) :
    perronMaxPatch w z p r q=w q := by
  apply if_neg
  intro hqin
  exact perron_boundary_not_open hq (hball (Metric.ball_subset_closedBall hqin))

end Yau.LeafProofs.L05Aux
