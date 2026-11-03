import Yau.Proofs.Y03Maximum

/-! The weak rectangle maximum principle follows by an arbitrarily small quadratic perturbation. -/

open scoped Topology
open Filter Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem secondDeriv_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t + g t)) x = deriv (deriv f) x + deriv (deriv g) x := by
  have heq : deriv (fun t => f t + g t) =ᶠ[𝓝 x] fun t => deriv f t + deriv g t := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with t hft hgt
    exact deriv_add (hft.differentiableAt (by norm_num)) (hgt.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_add ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem secondDeriv_quadratic (δ u x : ℝ) :
    deriv (deriv (fun t : ℝ => δ * (t ^ 2 + u ^ 2))) x = 2 * δ := by
  have heq : deriv (fun t : ℝ => δ * (t ^ 2 + u ^ 2)) = fun t => (2 * δ) * t := by
    funext t
    convert (((hasDerivAt_pow 2 t).add_const (u ^ 2)).const_mul δ).deriv using 1
    ring
  rw [heq]
  simp

theorem axisLaplacian_add_quadratic {f : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f z) (δ : ℝ) :
    axisLaplacian (fun p => f p + δ * (p.1 ^ 2 + p.2 ^ 2)) z =
      axisLaplacian f z + 4 * δ := by
  have hfx : ContDiffAt ℝ 2 (fun t => f (t, z.2)) z.1 :=
    hf.comp _ (contDiffAt_id.prodMk contDiffAt_const)
  have hfy : ContDiffAt ℝ 2 (fun t => f (z.1, t)) z.2 :=
    hf.comp _ (contDiffAt_const.prodMk contDiffAt_id)
  unfold axisLaplacian
  rw [secondDeriv_add hfx (by fun_prop), secondDeriv_add hfy (by fun_prop),
    secondDeriv_quadratic]
  have heq : (fun t : ℝ => δ * (z.1 ^ 2 + t ^ 2)) = fun t => δ * (t ^ 2 + z.1 ^ 2) := by
    funext t
    ring
  rw [heq, secondDeriv_quadratic]
  ring

theorem rectangle_weak_maximum {f : ℝ × ℝ → ℝ} {a b c d B : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hc : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (hf : ∀ z ∈ Ioo a b ×ˢ Ioo c d, ContDiffAt ℝ 2 f z)
    (hlap : ∀ z ∈ Ioo a b ×ˢ Ioo c d, 0 ≤ axisLaplacian f z)
    (hboundary : ∀ z ∈ Icc a b ×ˢ Icc c d,
      z.1 = a ∨ z.1 = b ∨ z.2 = c ∨ z.2 = d → f z ≤ B) :
    ∀ z ∈ Icc a b ×ˢ Icc c d, f z ≤ B := by
  let R := (|a| + |b|) ^ 2 + (|c| + |d|) ^ 2 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hbound : ∀ z ∈ Icc a b ×ˢ Icc c d, z.1 ^ 2 + z.2 ^ 2 ≤ R := by
    intro z hz
    have hxabs : |z.1| ≤ |a| + |b| := by
      apply abs_le.2
      constructor
      · have := neg_abs_le a
        linarith [hz.1.1, abs_nonneg b]
      · have := le_abs_self b
        linarith [hz.1.2, abs_nonneg a]
    have hyabs : |z.2| ≤ |c| + |d| := by
      apply abs_le.2
      constructor
      · have := neg_abs_le c
        linarith [hz.2.1, abs_nonneg d]
      · have := le_abs_self d
        linarith [hz.2.2, abs_nonneg c]
    have hxsq := pow_le_pow_left₀ (abs_nonneg z.1) hxabs 2
    have hysq := pow_le_pow_left₀ (abs_nonneg z.2) hyabs 2
    rw [sq_abs] at hxsq hysq
    dsimp [R]
    linarith
  intro z hz
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / R
  have hδ : 0 < δ := div_pos hε hR
  let g : ℝ × ℝ → ℝ := fun p => f p + δ * (p.1 ^ 2 + p.2 ^ 2)
  have hg : ∀ p ∈ Icc a b ×ˢ Icc c d, g p ≤ B + ε := by
    apply rectangle_strict_maximum hab hcd
    · exact hc.add (by fun_prop)
    · intro p hp
      rw [axisLaplacian_add_quadratic (hf p hp)]
      linarith [hlap p hp]
    · intro p hp hbdy
      have hB := hboundary p hp hbdy
      have hquad := mul_le_mul_of_nonneg_left (hbound p hp) hδ.le
      have hδR : δ * R = ε := by dsimp [δ]; field_simp
      dsimp [g]
      nlinarith
  have hgz := hg z hz
  have hnonneg : 0 ≤ δ * (z.1 ^ 2 + z.2 ^ 2) := by positivity
  dsimp [g] at hgz
  linarith

end Yau.Blueprint.Alignment.Y03Proof
