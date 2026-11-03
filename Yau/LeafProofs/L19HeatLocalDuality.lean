import Yau.LeafProofs.L19HeatLocalCaccioppoliAnnular
import Yau.LeafProofs.L19HeatWeightedEnergyMultiplier

/-! Compactly localized forward/backward heat duality on open time slabs. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux.LocalTime
open L18Aux
variable {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The exact Green commutator; all displayed integrals are actual integrable scalars. -/
theorem scalar_green_cutoff_commutator
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f k η : M.Carrier → ℝ}
    (hf : SmoothFn f) (hk : SmoothFn k) (hη : SmoothFn η)
    (hcη : HasCompactSupport η) :
    Integrable (fun x => η x * (k x * laplacian g.form f x -
      f x * laplacian g.form k x)) μ ∧
    Integrable (fun x => f x * scalarGradientPair g.form η k x -
      k x * scalarGradientPair g.form η f x) μ ∧
    (∫ x, η x * (k x * laplacian g.form f x -
      f x * laplacian g.form k x) ∂μ) =
      (1 / 2 : ℝ) * ∫ x, f x * scalarGradientPair g.form η k x -
        k x * scalarGradientPair g.form η f x ∂μ := by
  have hA := integral_scalar_green g hK μ hμ hf (smoothFn_mul hη hk) hcη.mul_right
  have hB := integral_scalar_green g hK μ hμ hk (smoothFn_mul hη hf) hcη.mul_right
  have heq : (fun x => f x * scalarGradientPair g.form η k x -
      k x * scalarGradientPair g.form η f x) =
      fun x => scalarGradientPair g.form (fun y => η y * f y) k x -
        scalarGradientPair g.form (fun y => η y * k y) f x := by
    funext x
    rw [scalarGradientPair_mul_left g.form hη hf,
      scalarGradientPair_mul_left g.form hη hk, scalarGradientPair_symm g.form f k]
    ring
  have heqL : (fun x => η x * (k x * laplacian g.form f x -
      f x * laplacian g.form k x)) =
      fun x => (η x * k x) * laplacian g.form f x -
        (η x * f x) * laplacian g.form k x := by funext x; ring
  rw [heqL, heq]
  refine ⟨hA.1.sub hB.1, hB.2.1.sub hA.2.1, ?_⟩
  rw [integral_sub hA.1 hB.1, integral_sub hB.2.1 hA.2.1, hA.2.2, hB.2.2]
  ring

/-- Differentiating the compact spatial pairing needs the heat equations only in I. -/
theorem scalarHeat_localized_pairing_hasDerivAt (hI : IsOpen I)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u v : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I) (hv : SmoothSpaceTime v I)
    (hforward : ∀ x t, t ∈ I → HasDerivAt (u x)
      (laplacian g.form (fun y => u y t) x) t)
    (hbackward : ∀ x t, t ∈ I → HasDerivAt (v x)
      (-laplacian g.form (fun y => v y t) x) t)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ x, η x * u x s * v x s ∂μ)
      ((1 / 2 : ℝ) * ∫ x, u x t * scalarGradientPair g.form η (fun y => v y t) x -
        v x t * scalarGradientPair g.form η (fun y => u y t) x ∂μ) t := by
  have hηt := smoothSpaceTime_spatial_const hI hη
  have hF : SmoothSpaceTime (fun x t => η x * u x t * v x t) I :=
    fun a => ((hηt a).mul (hu a)).mul (hv a)
  have hD : SmoothSpaceTime (fun x t => η x *
      (deriv (u x) t * v x t + u x t * deriv (v x) t)) I :=
    fun a => (hηt a).mul
      (((smoothSpaceTime_time_derivative hI hu a).mul (hv a)).add
        ((hu a).mul (smoothSpaceTime_time_derivative hI hv a)))
  have hd := (smoothSpaceTime_compact_integral_hasDerivAt hI g μ hμ hF hD hcη
    (fun x s _ hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun x s _ hx => by simp [image_eq_zero_of_notMem_tsupport hx]) (by
      intro x s hs
      have hdu := ((smoothSpaceTime_time_contDiffAt hu x (hI.mem_nhds hs)).differentiableAt
        (by simp)).hasDerivAt
      have hdv := ((smoothSpaceTime_time_contDiffAt hv x (hI.mem_nhds hs)).differentiableAt
        (by simp)).hasDerivAt
      convert (hdu.mul hdv).const_mul (η x) using 1
      funext r
      dsimp
      ring) ht).2.2
  have hval : (∫ x, η x * (deriv (u x) t * v x t + u x t * deriv (v x) t) ∂μ) =
      (1 / 2 : ℝ) * ∫ x, u x t * scalarGradientPair g.form η (fun y => v y t) x -
        v x t * scalarGradientPair g.form η (fun y => u y t) x ∂μ := by
    calc
      _ = ∫ x, η x * (v x t * laplacian g.form (fun y => u y t) x -
          u x t * laplacian g.form (fun y => v y t) x) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by dsimp only; rw [(hforward x t ht).deriv, (hbackward x t ht).deriv]; ring)
      _ = _ := (scalar_green_cutoff_commutator g hK μ hμ
        (smoothSpaceTime_slice hu ht) (smoothSpaceTime_slice hv ht) hη hcη).2.2
  rw [hval] at hd
  exact hd

/-- The integrated compact pairing identity on any compact interior time slab. -/
theorem scalarHeat_localized_pairing_interval_identity (hI : IsOpen I)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u v : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I) (hv : SmoothSpaceTime v I)
    (hforward : ∀ x t, t ∈ I → HasDerivAt (u x)
      (laplacian g.form (fun y => u y t) x) t)
    (hbackward : ∀ x t, t ∈ I → HasDerivAt (v x)
      (-laplacian g.form (fun y => v y t) x) t)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {s T : ℝ} (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    (∫ x, η x * u x T * v x T ∂μ) - (∫ x, η x * u x s * v x s ∂μ) =
      (1 / 2 : ℝ) * ∫ t in s..T, ∫ x,
        u x t * scalarGradientPair g.form η (fun y => v y t) x -
          v x t * scalarGradientPair g.form η (fun y => u y t) x ∂μ := by
  have hηt := smoothSpaceTime_spatial_const hI hη
  have hC : SmoothSpaceTime (fun x t =>
      u x t * scalarGradientPair g.form η (fun y => v y t) x -
        v x t * scalarGradientPair g.form η (fun y => u y t) x) I :=
    fun a => ((hu a).mul (smoothSpaceTime_scalarGradientPair hI g hηt hv a)).sub
      ((hv a).mul (smoothSpaceTime_scalarGradientPair hI g hηt hu a))
  have hCi := smoothSpaceTime_compact_integral_intervalIntegrable hI g μ hμ hC hcη
    (fun x t _ hx => by
      rw [scalarGradientPair_zero_of_notMem_tsupport g.form η _ hx,
        scalarGradientPair_zero_of_notMem_tsupport g.form η _ hx]
      ring) hslab hsT
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => scalarHeat_localized_pairing_hasDerivAt hI g hK μ hμ hu hv
      hforward hbackward hη hcη (hslab ((uIcc_of_le hsT).symm ▸ ht)))
    (hCi.const_mul (1 / 2 : ℝ))
  rw [intervalIntegral.integral_const_mul] at hFTC
  exact hFTC.symm

/-- The actual reversed flow is smooth on its genuine finite upper time domain. -/
theorem smoothSpaceTime_timeReverse {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Ioi 0)) (T₀ : ℝ) :
    SmoothSpaceTime (fun x t => u x (T₀ - t)) (Iio T₀) := by
  intro a
  apply (hu a).comp (contDiffOn_fst.prodMk (contDiffOn_const.sub contDiffOn_snd))
  intro p hp
  refine ⟨hp.1, ?_⟩
  change 0 < T₀ - p.2
  exact sub_pos.mpr hp.2

/-- Time reversal uses the forward PDE only at strictly positive source times. -/
theorem scalarHeat_timeReverse_hasDerivAt
    (g : SmoothMetric M) {u : M.Carrier → ℝ → ℝ}
    (hforward : ∀ x t, 0 < t → HasDerivAt (u x)
      (laplacian g.form (fun y => u y t) x) t)
    (T₀ : ℝ) (x : M.Carrier) {t : ℝ} (ht : t < T₀) :
    HasDerivAt (fun s => u x (T₀ - s))
      (-laplacian g.form (fun y => u y (T₀ - t)) x) t := by
  simpa only [Function.comp_def, sub_zero, zero_sub, mul_neg_one] using
    (hforward x (T₀ - t) (by linarith)).comp t
      ((hasDerivAt_const t T₀).sub (hasDerivAt_id t))

end Yau.LeafProofs.L19Aux.LocalTime
