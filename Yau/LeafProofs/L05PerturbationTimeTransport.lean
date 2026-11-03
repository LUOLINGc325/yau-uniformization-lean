import Yau.LeafProofs.L05PerturbationGeometry

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_center_mem_closed {n : ℕ} (z : Point n) {r : ℝ} (hr : 0<r)
    {p : Point n} (hp : p ∈ perturbClosed (0 : Space n) 1 0) :
    perturbCenter z r p ∈ perturbClosed z.1 r z.2 := by
  have hx : ‖p.1‖≤1 := by simpa using hp.1
  have ht : -(1 : ℝ)≤p.2 := by simpa using hp.2.1
  refine ⟨?_,?_,?_⟩
  · change dist (z.1+r • p.1) z.1≤r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  · change z.2-r^2≤z.2+r^2*p.2
    nlinarith [sq_nonneg r]
  · change z.2+r^2*p.2≤z.2
    nlinarith [sq_nonneg r,hp.2.2]

theorem perturb_center_mem_original {n : ℕ} {z : Point n} {r : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) : perturbCenter z r p ∈ backward 1 :=
  hbuf (perturb_center_mem_closed z hr ((perturbBack_subset_closed 0 1 0)
    (by simpa only [perturbBack_zero] using hp)))

theorem perturb_center_time_hasDerivWithinAt {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    HasDerivWithinAt (fun s => u (z.1+r • p.1,z.2+r^2*s))
      (r^2*timeD (backward 1) u (perturbCenter z r p))
      (Ioc (-(1 : ℝ)) 0) p.2 := by
  let x := z.1+r • p.1
  let t := z.2+r^2*p.2
  have hq := perturb_center_mem_original hr hbuf hp
  have hs : {s | (x,s) ∈ backward 1}=Ioc (-(1 : ℝ)) 0 := by
    ext s
    simp [backward,show x ∈ ball 0 1 from hq.1]
  have hd := (hu.2.2.2.2.2 _ hq).hasDerivWithinAt
  change HasDerivWithinAt (fun s => u (x,s))
    (timeD (backward 1) u (perturbCenter z r p)) {s | (x,s) ∈ backward 1} t at hd
  rw [hs] at hd
  have hm : MapsTo (fun s : ℝ => z.2+r^2*s) (Ioc (-1) 0) (Ioc (-1) 0) := by
    intro s hs'
    have hp' : (p.1,s) ∈ backward 1 := ⟨hp.1,by simpa using hs'⟩
    simpa only [perturbCenter,one_pow] using (perturb_center_mem_original hr hbuf hp').2
  have ht := ((hasDerivAt_id p.2).const_mul (r^2)).const_add z.2
  have hh := hd.comp p.2 ht.hasDerivWithinAt hm
  convert! hh using 1
  simp only [mul_one]
  ring

theorem perturb_center_timeD {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    timeD (backward 1) (fun q => u (perturbCenter z r q)) p=
      r^2*timeD (backward 1) u (perturbCenter z r p) := by
  have hd := perturb_center_time_hasDerivWithinAt hu z hr hbuf hp
  have hs : {s | (p.1,s) ∈ backward 1}=Ioc (-(1 : ℝ)) 0 := by
    ext s
    simp [backward,hp.1]
  unfold timeD
  rw [hs]
  exact hd.derivWithin (uniqueDiffOn_Ioc _ _ p.2 (by simpa using hp.2))


def perturbNormalize {n : ℕ} (u : Point n → ℝ) (z : Point n)
    (r N q0 : ℝ) (p : Point n) : ℝ :=
  (u (perturbCenter z r p)-u z-r^2*q0*p.2)/N

theorem perturb_normalize_time_hasDerivWithinAt {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    HasDerivWithinAt (fun s => perturbNormalize u z r N q0 (p.1,s))
      ((r^2/N)*(timeD (backward 1) u (perturbCenter z r p)-q0))
      (Ioc (-(1 : ℝ)) 0) p.2 := by
  have hu' := perturb_center_time_hasDerivWithinAt hu z hr hbuf hp
  have hl := ((hasDerivAt_id p.2).const_mul (r^2*q0)).hasDerivWithinAt
    (s := Ioc (-(1 : ℝ)) 0)
  have hh := ((hu'.sub_const (u z)).sub hl).div_const N
  convert! hh using 1
  simp only [mul_one]
  ring

theorem perturb_normalize_timeD {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    timeD (backward 1) (perturbNormalize u z r N q0) p=
      (r^2/N)*(timeD (backward 1) u (perturbCenter z r p)-q0) := by
  have hs : {s | (p.1,s) ∈ backward 1}=Ioc (-(1 : ℝ)) 0 := by
    ext s
    simp [backward,hp.1]
  change derivWithin (fun s => perturbNormalize u z r N q0 (p.1,s)) _ p.2 = _
  rw [hs]
  exact (perturb_normalize_time_hasDerivWithinAt hu z hr hbuf hp).derivWithin
    (uniqueDiffOn_Ioc _ _ p.2 (by simpa using hp.2))

end Yau.LeafProofs.L05Aux
