import Yau.LeafProofs.L05InitialCompletion
import Yau.LeafProofs.L16LocalTimeTransport

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic L16Aux

theorem timeD_cylinder_restrict_on_space {n : ℕ} {O S : Set (Space n)}
    {l r a b : ℝ} (hlr : l < r) (hO : O ⊆ S) (hal : a ≤ l) (hrb : r ≤ b)
    {u : Point n → ℝ} (hu : C2 (cylinder S a b) u) {p : Point n}
    (hp : p ∈ cylinder O l r) : timeD (cylinder O l r) u p=timeD (cylinder S a b) u p := by
  have hs : {t | (p.1,t) ∈ cylinder O l r}=Set.Icc l r := by ext t; simp [cylinder,hp.1]
  have hb : {t | (p.1,t) ∈ cylinder S a b}=Set.Icc a b := by ext t; simp [cylinder,hO hp.1]
  simp only [timeD,hs,hb]
  apply derivWithin_subset (Set.Icc_subset_Icc hal hrb) (uniqueDiffOn_Icc hlr p.2 hp.2)
  simpa only [hb] using hu.2.2.2.2.2 p ⟨hO hp.1,hal.trans hp.2.1,hp.2.2.trans hrb⟩

theorem c2_cylinder_restrict_on_space {n : ℕ} {O S : Set (Space n)}
    {l r a b : ℝ} (hlr : l < r) (hO : O ⊆ S) (hal : a ≤ l) (hrb : r ≤ b)
    {u : Point n → ℝ} (hu : C2 (cylinder S a b) u) : C2 (cylinder O l r) u := by
  have hs : cylinder O l r ⊆ cylinder S a b :=
    fun p hp => ⟨hO hp.1,hal.trans hp.2.1,hp.2.2.trans hrb⟩
  refine ⟨hu.1.mono hs,hu.2.1.mono hs,hu.2.2.1.mono hs,?_,
    fun p hp => hu.2.2.2.2.1 p (hs hp),?_⟩
  · exact (hu.2.2.2.1.mono hs).congr
      (fun p hp => timeD_cylinder_restrict_on_space hlr hO hal hrb hu hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p (hs hp)).mono (fun t ht => hs ht)

theorem c2_timeSlice_differentiableAt {n : ℕ} {O : Set (Space n)} {a b : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder O a b) u) {x : Space n} (hx : x ∈ O)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) : DifferentiableAt ℝ (fun s => u (x,s)) t := by
  have hh := hu.2.2.2.2.2 (x,t) ⟨hx,ht.1.le,ht.2.le⟩
  have hs : {s | (x,s) ∈ cylinder O a b}=Set.Icc a b := by ext s; simp [cylinder,hx]
  rw [hs] at hh
  exact hh.differentiableAt (Icc_mem_nhds ht.1 ht.2)

theorem timeD_cylinder_eq_deriv_of_interior {n : ℕ} {O : Set (Space n)} {a b : ℝ}
    (u : Point n → ℝ) {x : Space n} (hx : x ∈ O) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    timeD (cylinder O a b) u (x,t)=deriv (fun s => u (x,s)) t := by
  have hs : {s | (x,s) ∈ cylinder O a b}=Set.Icc a b := by ext s; simp [cylinder,hx]
  unfold timeD
  rw [hs]
  exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

theorem timeTranslatePoint_mem_buffer {n : ℕ} {O : Set (Space n)} {R a b tau : ℝ}
    (hO : Metric.ball 0 R ⊆ O) (ha : a < -(R^2)+tau) (hb : tau < b)
    {p : Point n} (hp : p ∈ backward R) :
    timeTranslatePoint tau p ∈ cylinder O a b ∧ p.2+tau ∈ Set.Ioo a b := by
  have hl : a < p.2+tau := by linarith only [ha,hp.2.1]
  have hr : p.2+tau < b := by linarith only [hb,hp.2.2]
  exact ⟨⟨hO hp.1,hl.le,hr.le⟩,hl,hr⟩

theorem timeD_timeTranslate_backward_buffer {n : ℕ} {O : Set (Space n)} {R a b tau : ℝ}
    (hO : Metric.ball 0 R ⊆ O) (ha : a < -(R^2)+tau) (hb : tau < b)
    {u : Point n → ℝ} (hu : C2 (cylinder O a b) u) {p : Point n} (hp : p ∈ backward R) :
    timeD (backward R) (timeTranslate tau u) p=
      timeD (cylinder O a b) u (timeTranslatePoint tau p) := by
  have hm := timeTranslatePoint_mem_buffer hO ha hb hp
  have hd := c2_timeSlice_differentiableAt hu (hO hp.1) hm.2
  have hh := hd.hasDerivAt.comp p.2 ((hasDerivAt_id p.2).add_const tau)
  have hs : {s | (p.1,s) ∈ backward R}=Set.Ioc (-(R^2)) 0 := by ext s; simp [backward,hp.1]
  change timeD (backward R) (timeTranslate tau u) p=timeD (cylinder O a b) u (p.1,p.2+tau)
  rw [timeD_cylinder_eq_deriv_of_interior u (hO hp.1) hm.2]
  unfold timeD
  rw [hs]
  convert! hh.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ioc _ _ p.2 hp.2) using 1 <;>
    simp only [mul_one]

theorem c2_timeTranslate_backward_buffer {n : ℕ} {O : Set (Space n)} {R a b tau : ℝ}
    (hO : Metric.ball 0 R ⊆ O) (ha : a < -(R^2)+tau) (hb : tau < b)
    {u : Point n → ℝ} (hu : C2 (cylinder O a b) u) : C2 (backward R) (timeTranslate tau u) := by
  have hm : Set.MapsTo (timeTranslatePoint tau) (backward R) (cylinder O a b) :=
    fun _ hp => (timeTranslatePoint_mem_buffer hO ha hb hp).1
  have hc : ContinuousOn (timeTranslatePoint (n := n) tau) (backward R) :=
    (timeTranslatePoint_contDiff tau).continuous.continuousOn
  refine ⟨hu.1.comp hc hm,hu.2.1.comp hc hm,hu.2.2.1.comp hc hm,?_,?_,?_⟩
  · exact (hu.2.2.2.1.comp hc hm).congr
      (fun p hp => timeD_timeTranslate_backward_buffer hO ha hb hu hp)
  · intro p hp
    exact hu.2.2.2.2.1 _ (hm hp)
  · intro p hp
    have hd := c2_timeSlice_differentiableAt hu (hO hp.1)
      (timeTranslatePoint_mem_buffer hO ha hb hp).2
    exact ((hd.comp p.2 ((hasDerivAt_id p.2).add_const tau).differentiableAt)).differentiableWithinAt

theorem holderBound_timeTranslate_set {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {gamma C tau : ℝ} {Q S : Set (Point n)} {f : Point n → V}
    (hm : Set.MapsTo (timeTranslatePoint tau) Q S) (hf : HolderBound gamma S f C) :
    HolderBound gamma Q (timeTranslate tau f) C := by
  refine ⟨hf.1,fun p hp => hf.2.1 _ (hm hp),?_⟩
  intro p hp q hq
  have hh := hf.2.2 _ (hm hp) _ (hm hq)
  simpa only [timeTranslate,timeTranslatePoint,holderWeight,add_sub_add_right_eq_sub] using hh

theorem hessian_timeTranslate {n : ℕ} (tau : ℝ) (u : Point n → ℝ) (p : Point n) :
    hessian (timeTranslate tau u) p=hessian u (timeTranslatePoint tau p) := rfl

end Yau.LeafProofs.L05Aux
