import Mathlib

/-!
The scalar estimate used before removing the spatial cutoffs in F04.
Only continuity is required at the initial face; the coefficient may be
singular there, with primitive `A * (t + t ^ β / β)` for `β > 0`.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

theorem integrating_factor_bound {S E : ℝ} (hS : 0 ≤ S) (hE : 0 ≤ E)
    {I I' B b : ℝ → ℝ}
    (hIc : ContinuousOn I (Icc 0 S)) (hI0 : I 0 = 0)
    (hBc : ContinuousOn B (Icc 0 S))
    (hBpos : ∀ s ∈ Icc 0 S, 0 ≤ B s)
    (hId : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hBd : ∀ s ∈ Ioo 0 S, HasDerivAt B (b s) s)
    (hbound : ∀ s ∈ Ioo 0 S, I' s ≤ b s * I s + E)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    I t ≤ E * t * Real.exp (B t) := by
  let g : ℝ → ℝ := fun s => Real.exp (-B s) * I s
  have hgc : ContinuousOn g (Icc 0 S) :=
    (Real.continuous_exp.comp_continuousOn hBc.neg).mul hIc
  have hgd (s : ℝ) (hs : s ∈ Ioo 0 S) :
      HasDerivAt g (Real.exp (-B s) * (I' s - b s * I s)) s := by
    convert ((hBd s hs).neg.exp.mul (hId s hs)) using 1
    change Real.exp (-B s) * (I' s - b s * I s) =
      Real.exp (-B s) * -b s * I s + Real.exp (-B s) * I' s
    ring
  have hgdiff : DifferentiableOn ℝ g (interior (Icc 0 S)) := by
    rw [interior_Icc]
    intro s hs
    exact (hgd s hs).differentiableAt.differentiableWithinAt
  have hgle : ∀ s ∈ interior (Icc 0 S), deriv g s ≤ E := by
    rw [interior_Icc]
    intro s hs
    rw [(hgd s hs).deriv]
    have hexp : 0 ≤ Real.exp (-B s) := (Real.exp_pos _).le
    have hexple : Real.exp (-B s) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hBpos s ⟨hs.1.le, hs.2.le⟩))
    calc
      Real.exp (-B s) * (I' s - b s * I s) ≤ Real.exp (-B s) * E :=
        mul_le_mul_of_nonneg_left (by linarith [hbound s hs]) hexp
      _ ≤ E := by nlinarith
  have hgt := (convex_Icc (0 : ℝ) S).image_sub_le_mul_sub_of_deriv_le
    hgc hgdiff hgle 0 ⟨le_rfl, hS⟩ t ht ht.1
  have hgt' : g t ≤ E * t := by simpa [g, hI0] using hgt
  have heq : Real.exp (B t) * Real.exp (-B t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    I t = Real.exp (B t) * g t := by
      dsimp [g]
      rw [← mul_assoc, heq, one_mul]
    _ ≤ Real.exp (B t) * (E * t) :=
      mul_le_mul_of_nonneg_left hgt' (Real.exp_pos _).le
    _ = E * t * Real.exp (B t) := by ring

def massPrimitive (A β t : ℝ) : ℝ := A * (t + t ^ β / β)

theorem massPrimitive_continuous (A β : ℝ) (hβ : 0 < β) :
    Continuous (massPrimitive A β) := by
  exact continuous_const.mul
    (continuous_id.add ((Real.continuous_rpow_const hβ.le).div_const β))

theorem massPrimitive_nonneg {A β t : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (ht : 0 ≤ t) : 0 ≤ massPrimitive A β t := by
  exact mul_nonneg hA (add_nonneg ht (div_nonneg (Real.rpow_nonneg ht β) hβ.le))

theorem massPrimitive_hasDerivAt (A β t : ℝ) (hβ : 0 < β) (ht : 0 < t) :
    HasDerivAt (massPrimitive A β) (A * (1 + t ^ (β - 1))) t := by
  have hr := (Real.hasDerivAt_rpow_const (x := t) (p := β) (Or.inl ht.ne')).div_const β
  change HasDerivAt (fun s : ℝ => A * (s + s ^ β / β)) _ t
  convert ((hasDerivAt_id t).add hr).const_mul A using 1
  · rfl
  · rw [mul_div_cancel_left₀ _ hβ.ne']

theorem finite_cutoff_gronwall {S A β E : ℝ} (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hβ : 0 < β) (hE : 0 ≤ E) {I I' : ℝ → ℝ}
    (hIc : ContinuousOn I (Icc 0 S)) (hI0 : I 0 = 0)
    (hId : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hbound : ∀ s ∈ Ioo 0 S,
      I' s ≤ A * (1 + s ^ (β - 1)) * I s + E)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    I t ≤ E * t * Real.exp (A * (t + t ^ β / β)) := by
  exact integrating_factor_bound hS hE hIc hI0
    (massPrimitive_continuous A β hβ).continuousOn
    (fun s hs => massPrimitive_nonneg hA hβ hs.1) hId
    (fun s hs => massPrimitive_hasDerivAt A β s hβ hs.1) hbound t ht

/-- Apply the finite-cutoff estimates first. The limit only concerns scalar
numbers, and requires no differentiation of an integral on the whole manifold. -/
theorem monotone_mass_eq_zero_of_error_tendsto {a e : ℕ → ℝ} (C : ℝ)
    (ha : Monotone a) (ha0 : ∀ m, 0 ≤ a m)
    (hbound : ∀ N, a N ≤ C * e N) (he : Tendsto e atTop (𝓝 0)) :
    ∀ m, a m = 0 := by
  intro m
  have hlim : Tendsto (fun N => C * e N) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul he
  have hle : a m ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop m] with N hN
    exact (ha hN).trans (hbound N))
  exact le_antisymm hle (ha0 m)

end Yau.F04Proof
