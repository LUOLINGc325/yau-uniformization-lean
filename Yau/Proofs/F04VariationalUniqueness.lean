import Yau.Proofs.F04SameTraceEnergy
import Yau.Proofs.F04WeakTimeSubtract
import Yau.Proofs.F04DualPairing
import Yau.LeafProofs.L16GalerkinEnergy

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.MassTargetStatements Yau.LeafProofs.L16HilbertTimeRegularization

variable {n : ℕ} {M : ComplexManifold n}

/-- Literal registered variational solutions have the same original continuous
 trace and the same actual energy curve. The single coercive pivot shift is
 handled by finite-time Gronwall. -/
theorem variationalSolution_unique_of_coercive
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure M.Carrier) (O : Set M.Carrier) {T : ℝ} (hT : 0 < T)
    (j : V →L[ℝ] FixedPivot μ O) (hj : ‖j‖ ≤ 1) (hjinj : Function.Injective j)
    (B : ℝ → V →L[ℝ] EnergyDual V) (α shift : ℝ) (hα : 0 < α) (hshift : 0 ≤ shift)
    (hcoerc : ∀ t ∈ Icc 0 T, ∀ v : V, α * ‖v‖ ^ 2 ≤ B t v v + shift * ‖j v‖ ^ 2)
    (f : ℝ → FixedPivot μ O) (U U₂ : ℝ → V) (R R₂ : ℝ → EnergyDual V)
    (a b : ℝ → FixedPivot μ O)
    (hsol : VariationalSolution μ O T j B f U R a)
    (hsol₂ : VariationalSolution μ O T j B f U₂ R₂ b) :
    (∀ t ∈ Icc 0 T, a t = b t) ∧ U =ᵐ[volume.restrict (Ioo 0 T)] U₂ := by
  have hw := variationalSolution_weak_time μ O hT j B f U R a hsol
  have hw₂ := variationalSolution_weak_time μ O hT j B f U₂ R₂ b hsol₂
  rcases hsol with ⟨hU, hR, ha, ha0, hae, _hw, hEq⟩
  rcases hsol₂ with ⟨hU₂, hR₂, hb, hb0, hbae, _hw₂, hEq₂⟩
  let UD := fun t => U t - U₂ t
  let RD := fun t => R t - R₂ t
  let Y := fun t => ‖a t - b t‖ ^ 2
  let F := fun t => RD t (UD t)
  have hUD : MemLp UD 2 (volume.restrict (Ioo 0 T)) := hU.sub hU₂
  have hRD : MemLp RD 2 (volume.restrict (Ioo 0 T)) := hR.sub hR₂
  have hwd := hilbert_weak_time_subtract j hT hU hU₂ hR hR₂ hw hw₂
  have hda : ∀ᵐ t ∂volume.restrict (Ioo 0 T), j (UD t) = a t - b t := by
    filter_upwards [hae, hbae] with t hat hbt
    dsimp only [UD]
    rw [map_sub, ← hat, ← hbt]
  have hchain := hilbert_weak_same_trace_energy j hj hT hUD hRD hwd
    (fun t => a t - b t) (ha.sub hb) hda
  have hYc : ContinuousOn Y (Icc 0 T) := (ha.sub hb).norm.pow 2
  have hY0 : Y 0 = 0 := by simp only [Y, ha0, hb0, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hFi : IntegrableOn F (Ioo 0 T) := dualPairing_integrable_L2 hUD hRD
  have hbound : F ≤ᵐ[volume.restrict (Ioo 0 T)] (fun t => shift * Y t) := by
    filter_upwards [hEq, hEq₂, hda, ae_restrict_mem measurableSet_Ioo] with t het he₂t hdt ht
    have heD : RD t (UD t) + B t (UD t) (UD t) = 0 := by
      have h1 := het (UD t)
      have h2 := he₂t (UD t)
      change (R t (UD t) - R₂ t (UD t)) + B t (U t - U₂ t) (UD t) = 0
      rw [(B t).map_sub (U t) (U₂ t)]
      change (R t (UD t) - R₂ t (UD t)) + (B t (U t) (UD t) - B t (U₂ t) (UD t)) = 0
      linarith only [h1, h2]
    have hc := hcoerc t (Ioo_subset_Icc_self ht) (UD t)
    rw [hdt] at hc
    have hα0 : 0 ≤ α * ‖UD t‖ ^ 2 := mul_nonneg hα.le (sq_nonneg _)
    change RD t (UD t) ≤ shift * ‖a t - b t‖ ^ 2
    linarith only [hc, hα0, heD]
  have hi : ∀ t ∈ Icc 0 T, Y t ≤ (2 * shift + 1) * (∫ s in (0 : ℝ)..t, Y s) + 0 := by
    intro t ht
    have hYi : IntervalIntegrable Y volume 0 t :=
      (hYc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hFit : IntegrableOn F (Ioo 0 t) := hFi.mono_set (Ioo_subset_Ioo le_rfl ht.2)
    have hYit := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp hYi
    have hbnd : F ≤ᵐ[volume.restrict (Ioo 0 t)] (fun s => shift * Y s) :=
      hbound.filter_mono (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2) le_rfl))
    have hcmp := integral_mono_ae hFit (hYit.const_mul shift) hbnd
    rw [integral_const_mul] at hcmp
    have hint : (∫ s in (0 : ℝ)..t, F s) ≤ shift * (∫ s in (0 : ℝ)..t, Y s) := by
      simpa only [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo] using hcmp
    have hc := hchain 0 ⟨le_rfl, hT.le⟩ t ht
    change Y t - Y 0 = 2 * ∫ s in (0 : ℝ)..t, F s at hc
    rw [hY0, sub_zero] at hc
    have hint0 : 0 ≤ ∫ s in (0 : ℝ)..t, Y s :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
    nlinarith
  have hg := Yau.LeafProofs.L16Aux.energy_integral_gronwall_on hT.le
    (by positivity : 0 < 2 * shift + 1) hYc hi
  have hab (t : ℝ) (ht : t ∈ Icc 0 T) : a t = b t := by
    have hYt : Y t = 0 := le_antisymm (by simpa only [mul_zero] using hg t ht) (sq_nonneg _)
    have hn : ‖a t - b t‖ = 0 := by
      change ‖a t - b t‖ ^ 2 = 0 at hYt
      nlinarith [norm_nonneg (a t - b t)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  refine ⟨hab, ?_⟩
  filter_upwards [hae, hbae, ae_restrict_mem measurableSet_Ioo] with t hat hbt ht
  apply hjinj
  rw [← hat, ← hbt]
  exact hab t (Ioo_subset_Icc_self ht)

end Yau.F04Proof
