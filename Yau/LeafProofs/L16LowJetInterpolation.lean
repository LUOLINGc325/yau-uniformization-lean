import Yau.LeafProofs.L16C2Interpolation

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Interpolation between a small uniform bound and spatial/parabolic Lipschitz
    bounds on a cylinder. -/
theorem holderBound_of_small_parabolic_lipschitz {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] {α ρ L a b : ℝ} {O : Set (Space n)}
    {f : Point n → V} (hα : 0 < α) (hα1 : α < 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 0 ≤ L)
    (hBound : ∀ p ∈ cylinder O a b, ‖f p‖ ≤ L*ρ)
    (hSpace : ∀ (x y : Space n) (t : ℝ), x ∈ O → y ∈ O →
      t ∈ Set.Icc a b → ‖f (x,t)-f (y,t)‖ ≤ L*‖x-y‖)
    (hTime : ∀ (x : Space n) (t v : ℝ), x ∈ O →
      t ∈ Set.Icc a b → v ∈ Set.Icc a b →
      ‖f (x,t)-f (x,v)‖ ≤ L*Real.sqrt |t-v|) :
    HolderBound α (cylinder O a b) f (2*L*ρ^(1-α)) := by
  have hBudget : 0 ≤ 2*L*ρ^(1-α) := by positivity
  have hρPow : ρ ≤ ρ^(1-α) :=
    Real.self_le_rpow_of_le_one hρ.le hρ1 (by linarith)
  have hAmp : L*ρ ≤ 2*L*ρ^(1-α) := by
    have h1 := mul_le_mul_of_nonneg_left hρPow hL
    have h2 : 0 ≤ L*ρ^(1-α) := by positivity
    nlinarith
  refine ⟨hBudget,fun p hp => (hBound p hp).trans hAmp,?_⟩
  intro p hp q hq
  let m : Point n := (q.1,p.2)
  have hm : m ∈ cylinder O a b := ⟨hq.1,hp.2⟩
  have h1Small : ‖f p-f m‖ ≤ 2*L*ρ := by
    calc
      _ ≤ ‖f p‖+‖f m‖ := norm_sub_le _ _
      _ ≤ L*ρ+L*ρ := add_le_add (hBound p hp) (hBound m hm)
      _ = _ := by ring
  have h2Small : ‖f m-f q‖ ≤ 2*L*ρ := by
    calc
      _ ≤ ‖f m‖+‖f q‖ := norm_sub_le _ _
      _ ≤ L*ρ+L*ρ := add_le_add (hBound m hm) (hBound q hq)
      _ = _ := by ring
  have h1 := small_lipschitz_holder_scale hρ (norm_nonneg (p.1-q.1)) hL hα hα1.le
    h1Small (hSpace p.1 q.1 p.2 hp.1 hq.1 hp.2)
  have h2 := small_lipschitz_holder_scale hρ (Real.sqrt_nonneg |p.2-q.2|) hL hα hα1.le
    h2Small (hTime q.1 p.2 q.2 hq.1 hp.2 hq.2)
  have hPow : (Real.sqrt |p.2-q.2|)^α = |p.2-q.2|^(α/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rw [hPow] at h2
  calc
    _ ≤ ‖f p-f m‖+‖f m-f q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*L*ρ^(1-α)*‖p.1-q.1‖^α+2*L*ρ^(1-α)*|p.2-q.2|^(α/2) :=
      add_le_add h1 h2
    _ = _ := by dsimp [holderWeight]; ring

/-- The actual low jet has an interior Hölder bound from the raw function,
    Hessian and time derivative bounds. No mixed derivative is required. -/
theorem c2_lowPair_interpolation {n : ℕ} {α s R a b ρ B K : ℝ} {u : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hab : a < b) (hs : 0 ≤ s)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hMargin : s+ρ ≤ R) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hu : C2 (cylinder (Metric.closedBall 0 R) a b) u)
    (huB : ∀ p ∈ cylinder (Metric.closedBall 0 R) a b, |u p| ≤ B)
    (huK : ∀ p ∈ cylinder (Metric.closedBall 0 R) a b,
      ‖spatialDD u p‖ ≤ K ∧ |timeD (cylinder (Metric.closedBall 0 R) a b) u p| ≤ K) :
    HolderBound α (cylinder (Metric.closedBall 0 s) a b) (fun p => (u p,spatialD u p))
      (8*(ρ^(1-α)*K+ρ^(-1-α)*B)) := by
  let G : ℝ := K*ρ+2*B/ρ
  let L : ℝ := 4*K+4*B/ρ^2
  have hHess : ∀ p ∈ cylinder (Metric.closedBall 0 R) a b, ‖spatialDD u p‖ ≤ K :=
    fun p hp => (huK p hp).1
  have hTime : ∀ p ∈ cylinder (Metric.closedBall 0 R) a b,
      |timeD (cylinder (Metric.closedBall 0 R) a b) u p| ≤ K :=
    fun p hp => (huK p hp).2
  have hSub : Metric.closedBall (0 : Space n) s ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have h4K : 4*K ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (by positivity)
  have hKL : K ≤ L := by linarith
  have hLρ : L*ρ = 4*K*ρ+4*B/ρ := by
    dsimp [L]
    field_simp
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
  have hGrad (x : Space n) (hx : x ∈ Metric.closedBall 0 s)
      (t : ℝ) (ht : t ∈ Set.Icc a b) : ‖spatialD u (x,t)‖ ≤ G :=
    c2_spatialD_sup_bound hu hHess huB hK hB hρ hMargin ht hx
  have hBound : ∀ p ∈ cylinder (Metric.closedBall 0 s) a b,
      ‖(u p,spatialD u p)‖ ≤ L*ρ := by
    intro p hp
    rw [Prod.norm_def]
    exact max_le ((huB p ⟨hSub hp.1,hp.2⟩).trans hBLρ)
      ((hGrad p.1 hp.1 p.2 hp.2).trans hGLρ)
  have hSpace : ∀ (x y : Space n) (t : ℝ), x ∈ Metric.closedBall 0 s →
      y ∈ Metric.closedBall 0 s → t ∈ Set.Icc a b →
      ‖(u (x,t),spatialD u (x,t))-(u (y,t),spatialD u (y,t))‖ ≤ L*‖x-y‖ := by
    intro x y t hx hy ht
    have hDiff (z : Space n) (hz : z ∈ Metric.closedBall 0 s) :
        DifferentiableAt ℝ (fun w => u (w,t)) z :=
      (hu.2.2.2.2.1 (z,t) ⟨hSub hz,ht⟩).differentiableAt (by norm_num)
    have hDeriv (z : Space n) (hz : z ∈ Metric.closedBall 0 s) :
        ‖fderiv ℝ (fun w => u (w,t)) z‖ ≤ G := hGrad z hz t ht
    have hValue := Convex.norm_image_sub_le_of_norm_fderiv_le hDiff hDeriv
      (convex_closedBall (0 : Space n) s) hy hx
    have hJet := c2_spatialD_lipschitz_on_closedBall hu hHess ht (hSub hx) (hSub hy)
    change max ‖u (x,t)-u (y,t)‖ ‖spatialD u (x,t)-spatialD u (y,t)‖ ≤ _
    exact max_le (hValue.trans (mul_le_mul_of_nonneg_right hGL (norm_nonneg _)))
      (hJet.trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _)))
  have hTemporal : ∀ (x : Space n) (t v : ℝ), x ∈ Metric.closedBall 0 s →
      t ∈ Set.Icc a b → v ∈ Set.Icc a b →
      ‖(u (x,t),spatialD u (x,t))-(u (x,v),spatialD u (x,v))‖ ≤ L*Real.sqrt |t-v| := by
    intro x t v hx ht hv
    change max |u (x,t)-u (x,v)| ‖spatialD u (x,t)-spatialD u (x,v)‖ ≤ _
    have hd : 0 ≤ Real.sqrt |t-v| := Real.sqrt_nonneg _
    rcases le_total (Real.sqrt |t-v|) ρ with hSmall | hLarge
    · have hValue := c2_time_lipschitz_on_closedBall hu hTime (hSub hx) hv ht
      have hJet := c2_spatialD_temporal_half_bound hu hHess hTime hK hMargin hx ht hv hSmall
      have hd1 : Real.sqrt |t-v| ≤ 1 := hSmall.trans hρ1
      have hdSq : (Real.sqrt |t-v|)^2 = |t-v| := Real.sq_sqrt (abs_nonneg _)
      have hValueBound : K*|t-v| ≤ L*Real.sqrt |t-v| := by
        calc
          _ ≤ K*Real.sqrt |t-v| := by
            apply mul_le_mul_of_nonneg_left _ hK
            nlinarith only [hdSq,mul_le_mul_of_nonneg_left hd1 hd]
          _ ≤ _ := mul_le_mul_of_nonneg_right hKL hd
      exact max_le (hValue.trans hValueBound)
        (hJet.trans (mul_le_mul_of_nonneg_right h4K hd))
    · have hScale : L*ρ ≤ L*Real.sqrt |t-v| := mul_le_mul_of_nonneg_left hLarge hL
      apply max_le
      · calc
          _ ≤ |u (x,t)|+|u (x,v)| := abs_sub _ _
          _ ≤ B+B := add_le_add (huB (x,t) ⟨hSub hx,ht⟩) (huB (x,v) ⟨hSub hx,hv⟩)
          _ = 2*B := by ring
          _ ≤ L*ρ := h2B
          _ ≤ _ := hScale
      · calc
          _ ≤ ‖spatialD u (x,t)‖+‖spatialD u (x,v)‖ := norm_sub_le _ _
          _ ≤ G+G := add_le_add (hGrad x hx t ht) (hGrad x hx v hv)
          _ = 2*G := by ring
          _ ≤ L*ρ := h2G
          _ ≤ _ := hScale
  have hHolder := holderBound_of_small_parabolic_lipschitz hα hα1 hρ hρ1 hL
    hBound hSpace hTemporal
  have hPow : ρ^(1-α)/ρ^2 = ρ^(-1-α) := by
    rw [← Real.rpow_two,← Real.rpow_sub hρ]
    congr 1
    ring
  have hBudget : 2*L*ρ^(1-α) = 8*(ρ^(1-α)*K+ρ^(-1-α)*B) := by
    dsimp [L]
    rw [← hPow]
    ring
  rwa [hBudget] at hHolder

end Yau.LeafProofs.L16Aux
