import Mathlib

/-! Compact upper contacts for the exponentially weighted comparison argument. -/

open Filter Set
open scoped Topology

namespace Yau.Proofs.F05Aux

theorem upperSemicontinuousWithinAt_pos_mul {Z : Type*} [TopologicalSpace Z]
    {D : Set Z} {x : Z} {f a : Z → ℝ}
    (hf : UpperSemicontinuousWithinAt f D x) (ha : ContinuousWithinAt a D x)
    (ha0 : 0 < a x) : UpperSemicontinuousWithinAt (fun z => a z * f z) D x := by
  intro r hr
  have hfr : f x < r / a x := (lt_div_iff₀ ha0).mpr (by simpa only [mul_comm] using hr)
  obtain ⟨b, hfb, hbr⟩ := exists_between hfr
  have hmul : a x * b < r := by
    simpa only [mul_comm] using (lt_div_iff₀ ha0).mp hbr
  have haevent : ∀ᶠ z in 𝓝[D] x, 0 < a z := ha (isOpen_Ioi.mem_nhds ha0)
  have hmul_event : ∀ᶠ z in 𝓝[D] x, a z * b < r :=
    (ha.mul_const b) (isOpen_Iio.mem_nhds hmul)
  filter_upwards [hf b hfb, haevent, hmul_event] with z hz haz hzb
  exact (mul_lt_mul_of_pos_left hz haz).trans hzb

theorem upperSemicontinuousOn_pos_mul {Z : Type*} [TopologicalSpace Z]
    {D : Set Z} {f a : Z → ℝ} (hf : UpperSemicontinuousOn f D)
    (ha : ContinuousOn a D) (ha0 : ∀ x ∈ D, 0 < a x) :
    UpperSemicontinuousOn (fun z => a z * f z) D := by
  intro x hx
  exact upperSemicontinuousWithinAt_pos_mul (hf x hx) (ha x hx) (ha0 x hx)

theorem compact_positive_max_interior {Z : Type*} [TopologicalSpace Z]
    (D : Set Z) (q : Z → ℝ) (hD : IsCompact D) (hq : UpperSemicontinuousOn q D)
    (hboundary : ∀ z ∈ D, z ∉ interior D → q z ≤ 0)
    (hpos : ∃ z ∈ D, 0 < q z) :
    ∃ z ∈ interior D, 0 < q z ∧ IsMaxOn q D z := by
  obtain ⟨z₀, hz₀, hq₀⟩ := hpos
  obtain ⟨z, hz, hmax⟩ := hq.exists_isMaxOn ⟨z₀, hz₀⟩ hD
  have hzpos : 0 < q z := hq₀.trans_le (hmax hz₀)
  refine ⟨z, ?_, hzpos, hmax⟩
  by_contra hn
  exact (not_lt_of_ge (hboundary z hz hn)) hzpos

/-- A weighted local maximum gives the actual upper touching function. -/
theorem weighted_max_touches {M : Type*} [TopologicalSpace M]
    (u v : M → ℝ → ℝ) (a b : ℝ → ℝ) (p : M × ℝ)
    (ha : ∀ t, 0 < a t)
    (hmax : IsLocalMax (fun z : M × ℝ => a z.2 * (v z.1 z.2 - u z.1 z.2) - b z.2) p) :
    let m := a p.2 * (v p.1 p.2 - u p.1 p.2) - b p.2
    (u p.1 p.2 + (m + b p.2) / a p.2 = v p.1 p.2) ∧
    ∀ᶠ z in 𝓝 p, v z.1 z.2 ≤ u z.1 z.2 + (m + b z.2) / a z.2 := by
  dsimp only
  constructor
  · field_simp [ne_of_gt (ha p.2)]
    ring
  · filter_upwards [hmax] with z hz
    have hzm : v z.1 z.2 - u z.1 z.2 ≤
        ((a p.2 * (v p.1 p.2 - u p.1 p.2) - b p.2) + b z.2) / a z.2 := by
      apply (le_div_iff₀ (ha z.2)).mpr
      nlinarith
    linarith

end Yau.Proofs.F05Aux
