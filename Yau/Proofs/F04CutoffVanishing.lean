import Yau.Proofs.F04FiniteMass

/-! Finite-cutoff estimates followed by a scalar limit, in the order used
by both the linear and nonlinear compact-mass arguments. -/

open Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

theorem cutoff_error_tendsto_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-δ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hδ).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

theorem finite_cutoff_mass_eq_zero {S A β D δ : ℝ}
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hβ : 0 < β) (hD : 0 ≤ D) (hδ : 0 < δ)
    (I I' : ℕ → ℝ → ℝ)
    (hIc : ∀ N, ContinuousOn (I N) (Icc 0 S)) (hI0 : ∀ N, I N 0 = 0)
    (hId : ∀ N s, s ∈ Ioo 0 S → HasDerivAt (I N) (I' N s) s)
    (hbound : ∀ N s, s ∈ Ioo 0 S →
      I' N s ≤ A * (1 + s ^ (β - 1)) * I N s + D * ((N : ℝ) + 1) ^ (-δ))
    (hpos : ∀ N s, s ∈ Icc 0 S → 0 ≤ I N s)
    (hmono : ∀ s, s ∈ Icc 0 S → Monotone (fun N => I N s)) :
    ∀ N s, s ∈ Icc 0 S → I N s = 0 := by
  intro N s hs
  apply monotone_mass_eq_zero_of_error_tendsto
    (D * s * Real.exp (A * (s + s ^ β / β))) (hmono s hs)
    (fun m => hpos m s hs) (e := fun m => ((m : ℝ) + 1) ^ (-δ))
  · intro m
    have hE : 0 ≤ D * ((m : ℝ) + 1) ^ (-δ) := by positivity
    have he := finite_cutoff_gronwall hS hA hβ hE (hIc m) (hI0 m)
      (hId m) (hbound m) s hs
    convert he using 1
    ring
  · exact cutoff_error_tendsto_zero hδ

end Yau.F04Proof
