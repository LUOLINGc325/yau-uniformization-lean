import Yau.Proofs.Y03Rectangle

/-! A bounded-strip maximum principle with an explicit positive harmonic barrier. -/

open scoped Topology
open Filter Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem secondDeriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t - g t)) x = deriv (deriv f) x - deriv (deriv g) x := by
  have heq : deriv (fun t => f t - g t) =ᶠ[𝓝 x] fun t => deriv f t - deriv g t := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with t hft hgt
    exact deriv_sub (hft.differentiableAt (by norm_num)) (hgt.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_sub ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem axisLaplacian_sub {f g : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    axisLaplacian (fun p => f p - g p) z = axisLaplacian f z - axisLaplacian g z := by
  unfold axisLaplacian
  rw [secondDeriv_sub (f := fun t => f (t, z.2)) (g := fun t => g (t, z.2))
      (hf.comp _ (contDiffAt_id.prodMk contDiffAt_const))
      (hg.comp _ (contDiffAt_id.prodMk contDiffAt_const)),
    secondDeriv_sub (f := fun t => f (z.1, t)) (g := fun t => g (z.1, t))
      (hf.comp _ (contDiffAt_const.prodMk contDiffAt_id))
      (hg.comp _ (contDiffAt_const.prodMk contDiffAt_id))]
  ring

theorem secondDeriv_cos_affine (κ a c x : ℝ) :
    deriv (deriv (fun t => c * Real.cos (κ * (t - a)))) x =
      -κ ^ 2 * (c * Real.cos (κ * (x - a))) := by
  have hinner : ∀ t : ℝ, HasDerivAt (fun t => κ * (t - a)) κ t := by
    intro t
    simpa using ((hasDerivAt_id t).sub_const a).const_mul κ
  have heq : deriv (fun t => c * Real.cos (κ * (t - a))) =
      fun t => -(c * κ) * Real.sin (κ * (t - a)) := by
    funext t
    convert ((hinner t).cos.const_mul c).deriv using 1
    ring
  rw [heq]
  convert ((hinner x).sin.const_mul (-(c * κ))).deriv using 1
  ring

theorem secondDeriv_cosh_linear (κ c x : ℝ) :
    deriv (deriv (fun t => c * Real.cosh (κ * t))) x =
      κ ^ 2 * (c * Real.cosh (κ * x)) := by
  have hinner : ∀ t : ℝ, HasDerivAt (fun t => κ * t) κ t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul κ
  have heq : deriv (fun t => c * Real.cosh (κ * t)) =
      fun t => (c * κ) * Real.sinh (κ * t) := by
    funext t
    convert ((hinner t).cosh.const_mul c).deriv using 1
    ring
  rw [heq]
  convert ((hinner x).sinh.const_mul (c * κ)).deriv using 1
  ring

def stripBarrier (T κ δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  δ * (Real.cos (κ * (z.1 - T / 2)) * Real.cosh (κ * z.2))

theorem stripBarrier_contDiff (T κ δ : ℝ) : ContDiff ℝ 2 (stripBarrier T κ δ) := by
  unfold stripBarrier
  fun_prop

theorem stripBarrier_axisLaplacian (T κ δ : ℝ) (z : ℝ × ℝ) :
    axisLaplacian (stripBarrier T κ δ) z = 0 := by
  have hx : (fun t => stripBarrier T κ δ (t, z.2)) =
      fun t => (δ * Real.cosh (κ * z.2)) * Real.cos (κ * (t - T / 2)) := by
    funext t
    unfold stripBarrier
    ring
  have hy : (fun t => stripBarrier T κ δ (z.1, t)) =
      fun t => (δ * Real.cos (κ * (z.1 - T / 2))) * Real.cosh (κ * t) := by
    funext t
    unfold stripBarrier
    ring
  unfold axisLaplacian
  rw [hx, hy, secondDeriv_cos_affine, secondDeriv_cosh_linear]
  ring

theorem stripBarrier_cos_lower {T x : ℝ} (hT : 0 < T) (hx : x ∈ Icc 0 T) :
    (1 / 2 : ℝ) ≤ Real.cos ((T + 1)⁻¹ * (x - T / 2)) := by
  have hden : 0 < T + 1 := by linarith
  have harg : |(T + 1)⁻¹ * (x - T / 2)| ≤ 1 / 2 := by
    rw [← div_eq_inv_mul, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    apply abs_le.2
    constructor <;> linarith [hx.1, hx.2]
  have hsq := pow_le_pow_left₀ (abs_nonneg ((T + 1)⁻¹ * (x - T / 2))) harg 2
  rw [sq_abs] at hsq
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (T + 1)⁻¹ * (x - T / 2))
  nlinarith

theorem bounded_strip_maximum {u : ℝ × ℝ → ℝ} {T B C : ℝ} (hT : 0 < T)
    (hc : ContinuousOn u (Icc 0 T ×ˢ univ))
    (hf : ∀ z ∈ Ioo 0 T ×ˢ univ, ContDiffAt ℝ 2 u z)
    (hlap : ∀ z ∈ Ioo 0 T ×ˢ univ, 0 ≤ axisLaplacian u z)
    (hbounded : ∀ z ∈ Icc 0 T ×ˢ univ, u z ≤ C)
    (hleft : ∀ y, u (0, y) ≤ B) (hright : ∀ y, u (T, y) ≤ B) :
    ∀ z ∈ Icc 0 T ×ˢ univ, u z ≤ B := by
  let κ := (T + 1)⁻¹
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcos : ∀ x ∈ Icc 0 T, 1 / 2 ≤ Real.cos (κ * (x - T / 2)) :=
    fun x hx => stripBarrier_cos_lower hT hx
  have hbarrier : ∀ δ, 0 < δ → ∀ z ∈ Icc 0 T ×ˢ univ,
      u z ≤ B + stripBarrier T κ δ z := by
    intro δ hδ z hz
    have hexp : Tendsto (fun R : ℝ => Real.exp (κ * R)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop hκ tendsto_id)
    obtain ⟨R₀, hR₀⟩ := (tendsto_atTop_atTop.1 hexp) (4 * (C - B) / δ)
    let R := max R₀ (|z.2| + 1)
    have hR₀' : R₀ ≤ R := le_max_left _ _
    have hRz : |z.2| + 1 ≤ R := le_max_right _ _
    have hRpos : 0 < R := by linarith [abs_nonneg z.2]
    have hδexp : C - B ≤ δ / 4 * Real.exp (κ * R) := by
      have hh := (div_le_iff₀ hδ).1 (hR₀ R hR₀')
      nlinarith
    have hhorizontal : ∀ x ∈ Icc 0 T,
        C - B ≤ stripBarrier T κ δ (x, R) := by
      intro x hx
      have hcosx := hcos x hx
      have hcosh : Real.exp (κ * R) / 2 ≤ Real.cosh (κ * R) := by
        rw [Real.cosh_eq]
        linarith [Real.exp_pos (-(κ * R))]
      have hmul := mul_le_mul_of_nonneg_right hcosx (Real.cosh_pos (κ * R)).le
      have hδmul := mul_le_mul_of_nonneg_left hmul hδ.le
      unfold stripBarrier
      dsimp only
      nlinarith
    have hbarpos : ∀ p ∈ Icc 0 T ×ˢ Icc (-R) R, 0 ≤ stripBarrier T κ δ p := by
      intro p hp
      exact mul_nonneg hδ.le (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans
        (hcos p.1 hp.1)) (Real.cosh_pos _).le)
    let v : ℝ × ℝ → ℝ := fun p => u p - stripBarrier T κ δ p
    have hrect : ∀ p ∈ Icc 0 T ×ˢ Icc (-R) R, v p ≤ B := by
      apply rectangle_weak_maximum hT.le (by linarith : -R ≤ R)
      · exact (hc.mono (prod_mono Subset.rfl (subset_univ _))).sub
          (stripBarrier_contDiff T κ δ).continuous.continuousOn
      · intro p hp
        exact (hf p ⟨hp.1, mem_univ _⟩).sub (stripBarrier_contDiff T κ δ).contDiffAt
      · intro p hp
        rw [axisLaplacian_sub (hf p ⟨hp.1, mem_univ _⟩)
          (stripBarrier_contDiff T κ δ).contDiffAt, stripBarrier_axisLaplacian, sub_zero]
        exact hlap p ⟨hp.1, mem_univ _⟩
      · intro p hp hbdy
        dsimp [v]
        rcases hbdy with hx | hx | hy | hy
        · have hh : u p ≤ B := by
            change u (p.1, p.2) ≤ B
            rw [hx]
            exact hleft p.2
          linarith [hbarpos p hp]
        · have hh : u p ≤ B := by
            change u (p.1, p.2) ≤ B
            rw [hx]
            exact hright p.2
          linarith [hbarpos p hp]
        · have hu := hbounded p ⟨hp.1, mem_univ _⟩
          have hb := hhorizontal p.1 hp.1
          have heq : stripBarrier T κ δ p = stripBarrier T κ δ (p.1, R) := by
            unfold stripBarrier
            rw [hy, mul_neg, Real.cosh_neg]
          rw [heq]
          linarith
        · have hu := hbounded p ⟨hp.1, mem_univ _⟩
          have hb := hhorizontal p.1 hp.1
          have heq : stripBarrier T κ δ p = stripBarrier T κ δ (p.1, R) := by
            unfold stripBarrier
            rw [hy]
          rw [heq]
          linarith
    have hzrect : z ∈ Icc 0 T ×ˢ Icc (-R) R := by
      exact ⟨hz.1, ⟨by linarith [neg_abs_le z.2], by linarith [le_abs_self z.2]⟩⟩
    have hh := hrect z hzrect
    dsimp [v] at hh
    linarith
  intro z hz
  let base := stripBarrier T κ 1 z
  have hbase : 0 ≤ base := by
    dsimp [base, stripBarrier]
    exact mul_nonneg zero_le_one (mul_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hcos z.1 hz.1)) (Real.cosh_pos _).le)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (base + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbase : δ * base ≤ ε := by
    change ε / (base + 1) * base ≤ ε
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < base + 1)).2
    nlinarith
  have hh := hbarrier δ hδ z hz
  have heq : stripBarrier T κ δ z = δ * base := by dsimp [stripBarrier, base]; ring
  rw [heq] at hh
  linarith

end Yau.Blueprint.Alignment.Y03Proof
