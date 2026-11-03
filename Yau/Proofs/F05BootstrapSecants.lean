import Yau.Proofs.F05BootstrapNative

/-! Mean-value and secant estimates use actual within derivatives on a convex
physical set. Every secant endpoint is required to lie on that same set. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_spatialD_lipschitz {X : Set (Space n)} {I : Set ℝ}
    {v : Point n → ℝ} {K : ℝ} (hv : F05RelC2 X I v)
    (hX : UniqueDiffOn ℝ X) (hcX : Convex ℝ X)
    (hK : ∀ z ∈ X ×ˢ I, ‖F05RelDD X v z‖ ≤ K)
    {t : ℝ} (ht : t ∈ I) {x y : Space n} (hx : x ∈ X) (hy : y ∈ X) :
    ‖F05RelD X v (x,t)-F05RelD X v (y,t)‖ ≤ K*‖x-y‖ := by
  have hDiff : DifferentiableOn ℝ (fun x => F05RelD X v (x,t)) X :=
    ((hv.2.2.2.2.1 t ht).fderivWithin hX (m := 1) (by norm_num)).differentiableOn
      (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hDiff z hz).hasFDerivWithinAt)
    (fun z hz => hK (z,t) ⟨hz,ht⟩) hcX hy hx

theorem F05_relative_spatial_lipschitz {X : Set (Space n)} {I : Set ℝ}
    {v : Point n → ℝ} {K : ℝ} (hv : F05RelC2 X I v) (hcX : Convex ℝ X)
    (hK : ∀ z ∈ X ×ˢ I, ‖F05RelD X v z‖ ≤ K)
    {t : ℝ} (ht : t ∈ I) {x y : Space n} (hx : x ∈ X) (hy : y ∈ X) :
    |v (x,t)-v (y,t)| ≤ K*‖x-y‖ := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((hv.2.2.2.2.1 t ht z hz).differentiableWithinAt
        (by norm_num)).hasFDerivWithinAt)
      (fun z hz => hK (z,t) ⟨hz,ht⟩) hcX hy hx

theorem F05_relative_time_lipschitz {X : Set (Space n)} {l r K : ℝ}
    {v : Point n → ℝ} (hv : F05RelC2 X (Icc l r) v)
    (hK : ∀ z ∈ X ×ˢ Icc l r, |F05RelT (Icc l r) v z| ≤ K)
    {x : Space n} (hx : x ∈ X) {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    |v (x,t)-v (x,s)| ≤ K*|t-s| := by
  have hDeriv (a : ℝ) (ha : a ∈ Icc l r) :
      HasDerivWithinAt (fun b => v (x,b)) (F05RelT (Icc l r) v (x,a)) (Icc l r) a :=
    (hv.2.2.2.2.2 (x,a) ⟨hx,ha⟩).hasDerivWithinAt
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hDeriv
      (fun a ha => by simpa only [Real.norm_eq_abs] using hK (x,a) ⟨hx,ha⟩)
      (convex_Icc l r) hs ht

theorem F05_relative_directional_taylor {X : Set (Space n)} {I : Set ℝ}
    {v : Point n → ℝ} {K ℓ : ℝ} (hv : F05RelC2 X I v)
    (hX : UniqueDiffOn ℝ X) (hcX : Convex ℝ X)
    (hK : ∀ z ∈ X ×ˢ I, ‖F05RelDD X v z‖ ≤ K)
    (hK0 : 0 ≤ K) (hℓ : 0 < ℓ) {t : ℝ} (ht : t ∈ I)
    {x : Space n} (hx : x ∈ X) (e : Space n) (he : ‖e‖ ≤ 1)
    (hEnd : x+ℓ • e ∈ X) :
    |v (x+ℓ • e,t)-v (x,t)-ℓ*F05RelD X v (x,t) e| ≤ K*ℓ^2 := by
  let G : Space n →L[ℝ] ℝ := F05RelD X v (x,t)
  let g : Space n → ℝ := fun y => v (y,t)-G y
  let S : Set (Space n) := X ∩ Metric.closedBall x ℓ
  have hDeriv (y : Space n) (hy : y ∈ S) :
      HasFDerivWithinAt g (F05RelD X v (y,t)-G) S y := by
    exact ((((hv.2.2.2.2.1 t ht y hy.1).differentiableWithinAt
      (by norm_num)).hasFDerivWithinAt).sub G.hasFDerivAt.hasFDerivWithinAt).mono
      inter_subset_left
  have hBound (y : Space n) (hy : y ∈ S) : ‖F05RelD X v (y,t)-G‖ ≤ K*ℓ := by
    have hLip := F05_relative_spatialD_lipschitz hv hX hcX hK ht hy.1 hx
    exact hLip.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy.2) hK0)
  have hEndBall : x+ℓ • e ∈ Metric.closedBall x ℓ := by
    rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hℓ]
    nlinarith
  have hMean := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hDeriv hBound
    (hcX.inter (convex_closedBall x ℓ))
    ⟨hx,Metric.mem_closedBall_self hℓ.le⟩ ⟨hEnd,hEndBall⟩
  have hExpr : g (x+ℓ • e)-g x =
      v (x+ℓ • e,t)-v (x,t)-ℓ*F05RelD X v (x,t) e := by
    dsimp only [g]
    rw [G.map_add,G.map_smul]
    simp only [smul_eq_mul]
    ring
  rw [hExpr,Real.norm_eq_abs,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_pos hℓ] at hMean
  exact hMean.trans (by nlinarith [mul_nonneg (mul_nonneg hK0 hℓ.le) hℓ.le])

theorem F05_relative_directional_secant {X : Set (Space n)} {I : Set ℝ}
    {v : Point n → ℝ} {K ℓ : ℝ} (hv : F05RelC2 X I v)
    (hX : UniqueDiffOn ℝ X) (hcX : Convex ℝ X)
    (hK : ∀ z ∈ X ×ˢ I, ‖F05RelDD X v z‖ ≤ K)
    (hK0 : 0 ≤ K) (hℓ : 0 < ℓ) {t : ℝ} (ht : t ∈ I)
    {x : Space n} (hx : x ∈ X) (e : Space n) (he : ‖e‖ ≤ 1)
    (hEnd : x+ℓ • e ∈ X) :
    |F05RelD X v (x,t) e-(v (x+ℓ • e,t)-v (x,t))/ℓ| ≤ K*ℓ := by
  have hTaylor := F05_relative_directional_taylor hv hX hcX hK hK0 hℓ ht hx e he hEnd
  have hExpr : F05RelD X v (x,t) e-(v (x+ℓ • e,t)-v (x,t))/ℓ =
      -(v (x+ℓ • e,t)-v (x,t)-ℓ*F05RelD X v (x,t) e)/ℓ := by
    field_simp
    ring
  rw [hExpr,abs_div,abs_neg,abs_of_pos hℓ]
  calc
    _ ≤ (K*ℓ^2)/ℓ := div_le_div_of_nonneg_right hTaylor hℓ.le
    _ = K*ℓ := by field_simp

end Yau.Proofs.F05Aux
