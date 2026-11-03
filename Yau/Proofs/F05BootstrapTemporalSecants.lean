import Yau.Proofs.F05BootstrapInwardSecants

/-! Comparing two genuine inward secants controls the time oscillation of
the gradient from the spatial Hessian and one-sided time derivative alone. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_cap_gradient_time_half (ν : Option (RIdx n))
    {v : Point n → ℝ} {R s l r K ρ : ℝ} (hR : 0 < R)
    (hv : F05RelC2 (region ν R) (Icc l r) v)
    (hHess : ∀ z ∈ region ν R ×ˢ Icc l r, ‖F05RelDD (region ν R) v z‖ ≤ K)
    (hTime : ∀ z ∈ region ν R ×ˢ Icc l r, |F05RelT (Icc l r) v z| ≤ K)
    (hK : 0 ≤ K) (hMargin : s+ρ ≤ R) {x : Space n} (hx : x ∈ region ν s)
    {t a : ℝ} (ht : t ∈ Icc l r) (ha : a ∈ Icc l r)
    (hSmall : Real.sqrt |t-a| ≤ ρ) :
    ‖F05RelD (region ν R) v (x,t)-F05RelD (region ν R) v (x,a)‖ ≤
      4*K*Real.sqrt |t-a| := by
  by_cases hta : t = a
  · subst t
    simp
  let ℓ : ℝ := Real.sqrt |t-a|
  have hℓ : 0 < ℓ := Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hta))
  have hℓSq : ℓ^2 = |t-a| := Real.sq_sqrt (abs_nonneg _)
  have hMarginℓ : s+ℓ ≤ R := by linarith
  have hxR : x ∈ region ν R := F05_region_mono (by linarith) hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  let d := F05InwardVector ν e
  have hd : ‖d‖ ≤ 1 := by rw [F05InwardVector_norm]; exact he.le
  have hEnd : x+ℓ • d ∈ region ν R :=
    F05_inward_secant_mem_region ν hx he.le hℓ.le hMarginℓ
  have hSecantT := F05_relative_directional_secant hv (F05_region_uniqueDiffOn ν hR)
    (F05_region_convex ν R) hHess hK hℓ ht hxR d hd hEnd
  have hSecantA := F05_relative_directional_secant hv (F05_region_uniqueDiffOn ν hR)
    (F05_region_convex ν R) hHess hK hℓ ha hxR d hd hEnd
  have hEndTime := F05_relative_time_lipschitz hv hTime hEnd ha ht
  have hBaseTime := F05_relative_time_lipschitz hv hTime hxR ha ht
  have hNumerator : |(v (x+ℓ • d,t)-v (x,t))-(v (x+ℓ • d,a)-v (x,a))| ≤
      2*K*|t-a| := by
    have hExpr : (v (x+ℓ • d,t)-v (x,t))-(v (x+ℓ • d,a)-v (x,a)) =
        (v (x+ℓ • d,t)-v (x+ℓ • d,a))-(v (x,t)-v (x,a)) := by ring
    rw [hExpr]
    exact (abs_sub _ _).trans ((add_le_add hEndTime hBaseTime).trans_eq (by ring))
  have hMiddle : |(v (x+ℓ • d,t)-v (x,t))/ℓ-(v (x+ℓ • d,a)-v (x,a))/ℓ| ≤
      2*K*ℓ := by
    rw [← sub_div,abs_div,abs_of_pos hℓ]
    calc
      _ ≤ (2*K*|t-a|)/ℓ := div_le_div_of_nonneg_right hNumerator hℓ.le
      _ = 2*K*ℓ := by rw [← hℓSq]; field_simp
  change |(F05RelD (region ν R) v (x,t)-F05RelD (region ν R) v (x,a)) e| ≤ _
  rw [← F05InwardVector_abs_apply ν e]
  change |F05RelD (region ν R) v (x,t) d-F05RelD (region ν R) v (x,a) d| ≤ _
  calc
    _ = |(F05RelD (region ν R) v (x,t) d-(v (x+ℓ • d,t)-v (x,t))/ℓ)+
        ((v (x+ℓ • d,t)-v (x,t))/ℓ-(v (x+ℓ • d,a)-v (x,a))/ℓ)+
        ((v (x+ℓ • d,a)-v (x,a))/ℓ-F05RelD (region ν R) v (x,a) d)| := by
      congr 1
      ring
    _ ≤ |F05RelD (region ν R) v (x,t) d-(v (x+ℓ • d,t)-v (x,t))/ℓ|+
        |(v (x+ℓ • d,t)-v (x,t))/ℓ-(v (x+ℓ • d,a)-v (x,a))/ℓ|+
        |(v (x+ℓ • d,a)-v (x,a))/ℓ-F05RelD (region ν R) v (x,a) d| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K*ℓ+2*K*ℓ+K*ℓ := add_le_add (add_le_add hSecantT hMiddle)
      (by simpa only [abs_sub_comm] using hSecantA)
    _ = 4*K*Real.sqrt |t-a| := by dsimp only [ℓ]; ring

end Yau.Proofs.F05Aux
