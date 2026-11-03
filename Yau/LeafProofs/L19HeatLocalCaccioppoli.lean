import Yau.LeafProofs.L19HeatLocalRegularity
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Space-time Caccioppoli for the actual scalar heat equation. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux.LocalTime
open L18Aux
variable {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Joint smoothness, with one fixed compact spatial support, gives
continuity of the actual spatial integral at every time in the open domain. -/
theorem smoothSpaceTime_compact_integral_continuousOn (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v I)
    {K : Set M.Carrier} (hK : IsCompact K)
    (hsupp : ∀ x t, t ∈ I → x ∉ K → v x t = 0) :
    ContinuousOn (fun t => ∫ x, v x t ∂μ) I := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  apply continuousOn_integral_of_compact_support (f := fun t x => v x t) hK
  · intro p hp
    exact ((smoothSpaceTime_continuousAt hI hv p.2 (t := p.1) hp.1).comp
      (f := Prod.swap) continuous_swap.continuousAt).continuousWithinAt
  · intro t x ht hx
    exact hsupp x t ht hx

/-- All spatial integrability and differentiation under the integral are
obtained from joint smoothness and a fixed compact spatial support. -/
theorem smoothSpaceTime_compact_integral_hasDerivAt (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v w : M.Carrier → ℝ → ℝ}
    (hv : SmoothSpaceTime v I) (hw : SmoothSpaceTime w I)
    {K : Set M.Carrier} (hK : IsCompact K)
    (hvsupp : ∀ x t, t ∈ I → x ∉ K → v x t = 0)
    (hwsupp : ∀ x t, t ∈ I → x ∉ K → w x t = 0)
    (hd : ∀ x t, t ∈ I → HasDerivAt (v x) (w x t) t)
    {t : ℝ} (ht : t ∈ I) :
    Integrable (fun x => v x t) μ ∧ Integrable (fun x => w x t) μ ∧
      HasDerivAt (fun s => ∫ x, v x s ∂μ) (∫ x, w x t ∂μ) t := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  have hiv (s : ℝ) (hs : s ∈ I) : Integrable (fun x => v x s) μ := by
    apply smoothFn_integrable_compact g μ hμ (smoothSpaceTime_slice hv hs)
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (hvsupp x s hs hxK)
  have hiw (s : ℝ) (hs : s ∈ I) : Integrable (fun x => w x s) μ := by
    apply smoothFn_integrable_compact g μ hμ (smoothSpaceTime_slice hw hs)
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (hwsupp x s hs hxK)
  obtain ⟨l, r, htlr, hloc, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hI.mem_nhds ht)
  have hc : ContinuousOn (fun p : M.Carrier × ℝ => ‖w p.1 p.2‖)
      (K ×ˢ Icc l r) := by
    intro p hp
    exact (smoothSpaceTime_continuousAt hI hw p.1 (hsub hp.2)).norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).bddAbove_image hc
  let b : M.Carrier → ℝ := K.indicator (fun _ => C)
  have hb : Integrable b μ :=
    (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s x => v x s) (F' := fun s x => w x s) (bound := b) hloc
    (by filter_upwards [hI.mem_nhds ht] with s hs using (hiv s hs).aestronglyMeasurable)
    (hiv t ht) (hiw t ht).aestronglyMeasurable
    (ae_of_all _ (fun x s hs => by
      by_cases hx : x ∈ K
      · exact (show ‖w x s‖ ≤ C from hC ⟨(x, s), ⟨hx, hs.1, hs.2⟩, rfl⟩).trans_eq
          (by simp [b, hx])
      · simp [b, hx, hwsupp x s (hsub hs) hx])) hb
    (ae_of_all _ (fun x s hs => hd x s (hsub hs)))
  exact ⟨hiv t ht, hdiff.1, hdiff.2⟩



/-- A project-smooth scalar is jointly smooth when kept constant in time. -/
theorem smoothSpaceTime_spatial_const (_hI : IsOpen I) {η : M.Carrier → ℝ} (hη : SmoothFn η) :
    SmoothSpaceTime (fun x _t => η x) I := by
  intro a
  exact (hη a).comp contDiffOn_fst (fun _ hp => hp.1)

/-- Compact spatial support makes every smooth open-time slice integrable. -/
theorem smoothSpaceTime_compact_slice_integrable (_hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v I)
    {K : Set M.Carrier} (hK : IsCompact K)
    (hsupp : ∀ x t, t ∈ I → x ∉ K → v x t = 0) {t : ℝ} (ht : t ∈ I) :
    Integrable (fun x => v x t) μ := by
  apply smoothFn_integrable_compact g μ hμ (smoothSpaceTime_slice hv ht)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro x hx
  by_contra hxK
  exact hx (hsupp x t ht hxK)

/-- The same compact-support construction supplies actual interval integrability. -/
theorem smoothSpaceTime_compact_integral_intervalIntegrable (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v I)
    {K : Set M.Carrier} (hK : IsCompact K)
    (hsupp : ∀ x t, t ∈ I → x ∉ K → v x t = 0)
    {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    IntervalIntegrable (fun t => ∫ x, v x t ∂μ) volume s T := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hsT]
  exact (smoothSpaceTime_compact_integral_continuousOn hI g μ hμ hv hK hsupp).mono
    hslab

/-- All spatial and time integrability in the Caccioppoli estimate follows
from the original joint smoothness, with no growth or mass assumption. -/
theorem scalarHeat_cutoff_integrable (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u I)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    (∀ t, t ∈ I →
      Integrable (fun x => η x ^ 2 * (u x t) ^ 2) μ ∧
      Integrable (fun x => η x ^ 2 * scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x) μ ∧
      Integrable (fun x => (u x t) ^ 2 * scalarGradientPair g.form η η x) μ) ∧
    IntervalIntegrable (fun t => ∫ x, η x ^ 2 * scalarGradientPair g.form
      (fun y => u y t) (fun y => u y t) x ∂μ) volume s T ∧
    IntervalIntegrable (fun t => ∫ x, (u x t) ^ 2 * scalarGradientPair g.form η η x ∂μ) volume s T := by
  have hηt := smoothSpaceTime_spatial_const hI hη
  have hA : SmoothSpaceTime (fun x t => η x ^ 2 *
      scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x) I :=
    fun a => ((hηt a).pow 2).mul (smoothSpaceTime_scalarGradientPair hI g hu hu a)
  have hB : SmoothSpaceTime (fun x t => (u x t) ^ 2 *
      scalarGradientPair g.form η η x) I :=
    fun a => ((hu a).pow 2).mul
      (smoothSpaceTime_spatial_const hI (smoothFn_scalarGradientPair g hη hη) a)
  have hF : SmoothSpaceTime (fun x t => η x ^ 2 * (u x t) ^ 2) I :=
    fun a => ((hηt a).pow 2).mul ((hu a).pow 2)
  have hAs (x : M.Carrier) (t : ℝ) (_ht : t ∈ I) (hx : x ∉ tsupport η) :
      η x ^ 2 * scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hBs (x : M.Carrier) (t : ℝ) (_ht : t ∈ I) (hx : x ∉ tsupport η) :
      (u x t) ^ 2 * scalarGradientPair g.form η η x = 0 := by
    rw [scalarGradientPair_zero_of_notMem_tsupport g.form η η hx, mul_zero]
  have hFs (x : M.Carrier) (t : ℝ) (_ht : t ∈ I) (hx : x ∉ tsupport η) :
      η x ^ 2 * (u x t) ^ 2 = 0 := by simp [image_eq_zero_of_notMem_tsupport hx]
  refine ⟨?_, smoothSpaceTime_compact_integral_intervalIntegrable hI g μ hμ hA hcη hAs hslab hsT,
    smoothSpaceTime_compact_integral_intervalIntegrable hI g μ hμ hB hcη hBs hslab hsT⟩
  intro t ht
  exact ⟨smoothSpaceTime_compact_slice_integrable hI g μ hμ hF hcη hFs ht,
    smoothSpaceTime_compact_slice_integrable hI g μ hμ hA hcη hAs ht,
    smoothSpaceTime_compact_slice_integrable hI g μ hμ hB hcη hBs ht⟩

/-- Exact derivative of the compactly localized squared scalar, before
using either forward or backward heat evolution. -/
theorem scalarHeat_cutoff_square_hasDerivAt (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u I)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ x, η x ^ 2 * (u x s) ^ 2 ∂μ)
      (∫ x, 2 * η x ^ 2 * u x t * deriv (u x) t ∂μ) t := by
  have hηt := smoothSpaceTime_spatial_const hI hη
  have hv : SmoothSpaceTime (fun x t => η x ^ 2 * (u x t) ^ 2) I :=
    fun a => ((hηt a).pow 2).mul ((hu a).pow 2)
  have hw : SmoothSpaceTime (fun x t => 2 * η x ^ 2 * u x t * deriv (u x) t) I :=
    fun a => (((contDiffOn_const.mul ((hηt a).pow 2)).mul (hu a)).mul
      (smoothSpaceTime_time_derivative hI hu a))
  apply (smoothSpaceTime_compact_integral_hasDerivAt hI g μ hμ hv hw hcη
    (fun x s _ hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun x s _ hx => by simp [image_eq_zero_of_notMem_tsupport hx]) ?_ ht).2.2
  intro x s hs
  have hd := ((smoothSpaceTime_time_contDiffAt hu x (hI.mem_nhds hs)).differentiableAt
    (by simp)).hasDerivAt
  convert (hd.pow 2).const_mul (η x ^ 2) using 1 <;> ring



/-- A signed genuine heat equation gives the stronger endpoint identity
form of space-time Caccioppoli. The two signs are forward and backward heat. -/
theorem scalarHeat_caccioppoli_signed (hI : IsOpen I)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I) (a : ℝ) (ha : a ^ 2 = 1)
    (hheat : ∀ x t, t ∈ I → HasDerivAt (u x)
      (a * laplacian g.form (fun y => u y t) x) t)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    (∫ t in s..T, ∫ x, η x ^ 2 * scalarGradientPair g.form
      (fun y => u y t) (fun y => u y t) x ∂μ) ≤
      2 * a * (∫ x, η x ^ 2 * (u x s) ^ 2 ∂μ) -
      2 * a * (∫ x, η x ^ 2 * (u x T) ^ 2 ∂μ) +
      4 * ∫ t in s..T, ∫ x, (u x t) ^ 2 * scalarGradientPair g.form η η x ∂μ := by
  let A : ℝ → ℝ := fun t => ∫ x, η x ^ 2 * scalarGradientPair g.form
    (fun y => u y t) (fun y => u y t) x ∂μ
  let B : ℝ → ℝ := fun t => ∫ x, (u x t) ^ 2 * scalarGradientPair g.form η η x ∂μ
  let F : ℝ → ℝ := fun t => ∫ x, η x ^ 2 * (u x t) ^ 2 ∂μ
  let D : ℝ → ℝ := fun t => ∫ x, 2 * η x ^ 2 * u x t * deriv (u x) t ∂μ
  have hreg := scalarHeat_cutoff_integrable hI g μ hμ hu hη hcη hslab hsT
  have hηt := smoothSpaceTime_spatial_const hI hη
  have hw : SmoothSpaceTime (fun x t => 2 * η x ^ 2 * u x t * deriv (u x) t) I :=
    fun q => (((contDiffOn_const.mul ((hηt q).pow 2)).mul (hu q)).mul
      (smoothSpaceTime_time_derivative hI hu q))
  have hDint : IntervalIntegrable D volume s T :=
    smoothSpaceTime_compact_integral_intervalIntegrable hI g μ hμ hw hcη
      (fun x t _ hx => by simp [image_eq_zero_of_notMem_tsupport hx]) hslab hsT
  have hFTC : (∫ t in s..T, D t) = F T - F s := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hDint
    intro t ht
    exact scalarHeat_cutoff_square_hasDerivAt hI g μ hμ hu hη hcη
      (hslab ((uIcc_of_le hsT).symm ▸ ht))
  have hlocal (t : ℝ) (ht : t ∈ Icc s T) : A t + (2 * a) * D t ≤ 4 * B t := by
    have ht0 := hslab ht
    have hut := smoothSpaceTime_slice hu ht0
    let ψ : M.Carrier → ℝ := fun x => η x * η x * u x t
    have hψ : SmoothFn ψ := smoothFn_mul (smoothFn_mul hη hη) hut
    have hcψ : HasCompactSupport ψ := hcη.mul_right.mul_right
    have hG := integral_scalar_green g hK μ hμ hut hψ hcψ
    have hp := integral_mono (hreg.1 t ht0).2.1
      (((hreg.1 t ht0).2.2.const_mul 4).add (hG.2.1.const_mul 2))
      (scalar_caccioppoli_point g.form hut hη)
    change A t ≤ ∫ x, 4 * ((u x t) ^ 2 * scalarGradientPair g.form η η x) +
      2 * scalarGradientPair g.form ψ (fun y => u y t) x ∂μ at hp
    rw [integral_add ((hreg.1 t ht0).2.2.const_mul 4) (hG.2.1.const_mul 2),
      integral_const_mul, integral_const_mul] at hp
    have hDval : D t = (2 * a) * ∫ x, ψ x * laplacian g.form (fun y => u y t) x ∂μ := by
      calc
        D t = ∫ x, (2 * a) * (ψ x * laplacian g.form (fun y => u y t) x) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ (fun x => by dsimp only; rw [(hheat x t ht0).deriv]; dsimp [ψ]; ring)
        _ = _ := integral_const_mul _ _
    have hnum : (2 * a) * D t = 4 * ∫ x, ψ x * laplacian g.form (fun y => u y t) x ∂μ := by
      rw [hDval]
      calc
        (2 * a) * ((2 * a) * ∫ x, ψ x * laplacian g.form (fun y => u y t) x ∂μ) =
          4 * a ^ 2 * ∫ x, ψ x * laplacian g.form (fun y => u y t) x ∂μ := by ring
        _ = _ := by rw [ha]; ring
    dsimp only [B]
    nlinarith [hG.2.2]
  have hi := intervalIntegral.integral_mono_on hsT (hreg.2.1.add (hDint.const_mul (2 * a)))
    (hreg.2.2.const_mul 4) hlocal
  rw [intervalIntegral.integral_add hreg.2.1 (hDint.const_mul (2 * a)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC] at hi
  change (∫ t in s..T, A t) ≤ 2 * a * F s - 2 * a * F T + 4 * ∫ t in s..T, B t
  linarith

/-- Forward actual heat Caccioppoli, with no positivity, growth or mass hypotheses. -/
theorem scalarHeat_caccioppoli_forward (hI : IsOpen I)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I)
    (hheat : ∀ x t, t ∈ I → HasDerivAt (u x)
      (laplacian g.form (fun y => u y t) x) t)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    (∫ t in s..T, ∫ x, η x ^ 2 * scalarGradientPair g.form
      (fun y => u y t) (fun y => u y t) x ∂μ) ≤
      2 * (∫ x, η x ^ 2 * (u x s) ^ 2 ∂μ) +
      4 * ∫ t in s..T, ∫ x, (u x t) ^ 2 * scalarGradientPair g.form η η x ∂μ := by
  have h := scalarHeat_caccioppoli_signed hI g hK μ hμ hu 1 (by norm_num)
    (fun x t ht => by simpa only [one_mul] using hheat x t ht) hη hcη hslab hsT
  have hnonneg : 0 ≤ ∫ x, η x ^ 2 * (u x T) ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith

/-- Backward actual heat Caccioppoli, with the terminal squared scalar. -/
theorem scalarHeat_caccioppoli_backward (hI : IsOpen I)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I)
    (hheat : ∀ x t, t ∈ I → HasDerivAt (u x)
      (-laplacian g.form (fun y => u y t) x) t)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    (∫ t in s..T, ∫ x, η x ^ 2 * scalarGradientPair g.form
      (fun y => u y t) (fun y => u y t) x ∂μ) ≤
      2 * (∫ x, η x ^ 2 * (u x T) ^ 2 ∂μ) +
      4 * ∫ t in s..T, ∫ x, (u x t) ^ 2 * scalarGradientPair g.form η η x ∂μ := by
  have h := scalarHeat_caccioppoli_signed hI g hK μ hμ hu (-1) (by norm_num)
    (fun x t ht => by simpa only [neg_mul, one_mul] using hheat x t ht) hη hcη hslab hsT
  have hnonneg : 0 ≤ ∫ x, η x ^ 2 * (u x s) ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith

end Yau.LeafProofs.L19Aux.LocalTime
