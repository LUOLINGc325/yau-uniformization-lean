import Yau.Proofs.F05BootstrapTemporalSecants

/-! The small interpolation factor at the physical boundary follows from
inward secants. There is no mixed derivative or lower-jet Hölder premise. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_cap_low_interpolation (ν : Option (RIdx n))
    {α s R a b ρ B K : ℝ} {v : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hMargin : s+ρ ≤ R)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hv : F05RelC2 (region ν R) (Icc a b) v)
    (hvB : ∀ z ∈ region ν R ×ˢ Icc a b, |v z| ≤ B)
    (hvK : ∀ z ∈ region ν R ×ˢ Icc a b,
      ‖F05RelDD (region ν R) v z‖ ≤ K ∧ |F05RelT (Icc a b) v z| ≤ K) :
    HolderBound α (region ν s ×ˢ Icc a b)
      (fun z => (v z,F05RelD (region ν R) v z))
      (8*(ρ^(1-α)*K+ρ^(-1-α)*B)) := by
  let G : ℝ := K*ρ+2*B/ρ
  let L : ℝ := 4*K+4*B/ρ^2
  have hHess : ∀ z ∈ region ν R ×ˢ Icc a b, ‖F05RelDD (region ν R) v z‖ ≤ K :=
    fun z hz => (hvK z hz).1
  have hTime : ∀ z ∈ region ν R ×ˢ Icc a b, |F05RelT (Icc a b) v z| ≤ K :=
    fun z hz => (hvK z hz).2
  have hSub : region ν s ⊆ region ν R := F05_region_mono (by linarith)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have h4K : 4*K ≤ L := by dsimp [L]; exact le_add_of_nonneg_right (by positivity)
  have hKL : K ≤ L := by linarith
  have hLρ : L*ρ = 4*K*ρ+4*B/ρ := by dsimp [L]; field_simp
  have h2G : 2*G ≤ L*ρ := by
    rw [hLρ]
    dsimp [G]
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg hK hρ.le]
  have hBdiv : B ≤ B/ρ := by
    apply (le_div_iff₀ hρ).mpr
    nlinarith
  have h2B : 2*B ≤ L*ρ := by
    rw [hLρ]
    simp only [div_eq_mul_inv] at hBdiv ⊢
    nlinarith [mul_nonneg hK hρ.le]
  have hGLρ : G ≤ L*ρ := by linarith
  have hBLρ : B ≤ L*ρ := by linarith
  have hLρL : L*ρ ≤ L := mul_le_of_le_one_right hL hρ1
  have hGL : G ≤ L := hGLρ.trans hLρL
  have hGrad (x : Space n) (hx : x ∈ region ν s) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖F05RelD (region ν R) v (x,t)‖ ≤ G :=
    F05_relative_cap_gradient_bound ν hR hv hHess hvB hK hB hρ hMargin ht hx
  have hBound : ∀ z ∈ region ν s ×ˢ Icc a b,
      ‖(v z,F05RelD (region ν R) v z)‖ ≤ L*ρ := by
    intro z hz
    rw [Prod.norm_def]
    exact max_le ((hvB z ⟨hSub hz.1,hz.2⟩).trans hBLρ)
      ((hGrad z.1 hz.1 z.2 hz.2).trans hGLρ)
  have hSpace : ∀ (x y : Space n) (t : ℝ), x ∈ region ν s → y ∈ region ν s →
      t ∈ Icc a b → ‖(v (x,t),F05RelD (region ν R) v (x,t))-
        (v (y,t),F05RelD (region ν R) v (y,t))‖ ≤ L*‖x-y‖ := by
    intro x y t hx hy ht
    have hDeriv (z : Space n) (hz : z ∈ region ν s) :
        HasFDerivWithinAt (fun w => v (w,t)) (F05RelD (region ν R) v (z,t))
          (region ν s) z :=
      (((hv.2.2.2.2.1 t ht z (hSub hz)).differentiableWithinAt
        (by norm_num)).hasFDerivWithinAt).mono hSub
    have hValue := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hDeriv
      (fun z hz => hGrad z hz t ht) (F05_region_convex ν s) hy hx
    have hJet := F05_relative_spatialD_lipschitz hv (F05_region_uniqueDiffOn ν hR)
      (F05_region_convex ν R) hHess ht (hSub hx) (hSub hy)
    change max ‖v (x,t)-v (y,t)‖
      ‖F05RelD (region ν R) v (x,t)-F05RelD (region ν R) v (y,t)‖ ≤ _
    exact max_le (hValue.trans (mul_le_mul_of_nonneg_right hGL (norm_nonneg _)))
      (hJet.trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _)))
  have hTemporal : ∀ (x : Space n) (t u : ℝ), x ∈ region ν s → t ∈ Icc a b →
      u ∈ Icc a b → ‖(v (x,t),F05RelD (region ν R) v (x,t))-
        (v (x,u),F05RelD (region ν R) v (x,u))‖ ≤ L*Real.sqrt |t-u| := by
    intro x t u hx ht hu
    change max |v (x,t)-v (x,u)|
      ‖F05RelD (region ν R) v (x,t)-F05RelD (region ν R) v (x,u)‖ ≤ _
    have hd : 0 ≤ Real.sqrt |t-u| := Real.sqrt_nonneg _
    rcases le_total (Real.sqrt |t-u|) ρ with hSmall | hLarge
    · have hValue := F05_relative_time_lipschitz hv hTime (hSub hx) hu ht
      have hJet := F05_relative_cap_gradient_time_half ν hR hv hHess hTime hK hMargin hx ht hu hSmall
      have hd1 : Real.sqrt |t-u| ≤ 1 := hSmall.trans hρ1
      have hdSq : (Real.sqrt |t-u|)^2 = |t-u| := Real.sq_sqrt (abs_nonneg _)
      have hValueBound : K*|t-u| ≤ L*Real.sqrt |t-u| := by
        calc
          _ ≤ K*Real.sqrt |t-u| := by
            apply mul_le_mul_of_nonneg_left _ hK
            nlinarith only [hdSq,mul_le_mul_of_nonneg_left hd1 hd]
          _ ≤ _ := mul_le_mul_of_nonneg_right hKL hd
      exact max_le (hValue.trans hValueBound)
        (hJet.trans (mul_le_mul_of_nonneg_right h4K hd))
    · have hScale : L*ρ ≤ L*Real.sqrt |t-u| := mul_le_mul_of_nonneg_left hLarge hL
      apply max_le
      · calc
          _ ≤ |v (x,t)|+|v (x,u)| := abs_sub _ _
          _ ≤ B+B := add_le_add (hvB (x,t) ⟨hSub hx,ht⟩) (hvB (x,u) ⟨hSub hx,hu⟩)
          _ = 2*B := by ring
          _ ≤ L*ρ := h2B
          _ ≤ _ := hScale
      · calc
          _ ≤ ‖F05RelD (region ν R) v (x,t)‖+‖F05RelD (region ν R) v (x,u)‖ := norm_sub_le _ _
          _ ≤ G+G := add_le_add (hGrad x hx t ht) (hGrad x hx u hu)
          _ = 2*G := by ring
          _ ≤ L*ρ := h2G
          _ ≤ _ := hScale
  have hHolder := holderBound_of_small_parabolic_lipschitz hα hα1 hρ hρ1 hL hBound hSpace hTemporal
  have hPow : ρ^(1-α)/ρ^2 = ρ^(-1-α) := by
    rw [← Real.rpow_two,← Real.rpow_sub hρ]
    congr 1
    ring
  have hBudget : 2*L*ρ^(1-α) = 8*(ρ^(1-α)*K+ρ^(-1-α)*B) := by
    dsimp [L]
    rw [← hPow]
    ring
  rwa [hBudget] at hHolder

end Yau.Proofs.F05Aux
