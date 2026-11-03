import Yau.Proofs.F04GalerkinEvolution
import Yau.Proofs.F04CoerciveScalarBound

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}

/-- The estimate is derived from the native primitive identity for the actual
 Galerkin equation. Its constants precede the forcing and the finite space. -/
theorem variationalGalerkin_uniform {T C α shift : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hα : 0 < α) (hshift : 0 ≤ shift)
    (j : V →L[ℝ] H) (e : Fin m → V) (he : Orthonormal ℝ (fun i => j (e i)))
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hcB : ∀ u v, Continuous (fun t => B t u v))
    (hGard : ∀ t ∈ Icc 0 T, ∀ v : V, α * ‖v‖ ^ 2 ≤ B t v v + shift * ‖j v‖ ^ 2)
    {F : ℝ → H} (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    {c : ℝ → EuclideanSpace ℝ (Fin m)} (hc : ContinuousOn c (Icc 0 T))
    (hcEq : ∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
      variationalForcing j e (F s) - variationalMatrix e (B s) (c s)) :
    (∀ t ∈ Icc 0 T, ‖j (variationalReconstruction e (c t))‖ ^ 2 ≤
      coerciveTimeBound T (2 * shift + 1) * (∫ s in Ioo 0 T, ‖F s‖ ^ 2)) ∧
    (∫ s in Ioo 0 T, ‖variationalReconstruction e (c s)‖ ^ 2) ≤
      coerciveEnergyBound T (2 * α) (2 * shift + 1) * (∫ s in Ioo 0 T, ‖F s‖ ^ 2) := by
  let rhs := fun t => variationalForcing j e (F t) - variationalMatrix e (B t) (c t)
  let y := fun t => ‖c t‖ ^ 2
  let z := fun t => ‖variationalReconstruction e (c t)‖ ^ 2
  let q := fun t => ‖F t‖ ^ 2
  have hy : ContinuousOn y (Icc 0 T) := hc.norm.pow 2
  have hz : ContinuousOn z (Icc 0 T) :=
    ((variationalReconstruction e).continuous.comp_continuousOn hc).norm.pow 2
  have hqi : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr
      ((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF)
  have hrhs : Integrable rhs (volume.restrict (Ioo 0 T)) :=
    variationalGalerkin_rhs_integrable hT.le hC j e B hB hcB hF hc
  have hcPrim : ∀ t ∈ Icc 0 T, c t = (0 : EuclideanSpace ℝ (Fin m)) + ∫ s in (0 : ℝ)..t, rhs s := by
    simpa only [zero_add] using hcEq
  have hc0 : c 0 = 0 := by simpa using hcEq 0 ⟨le_rfl, hT.le⟩
  have henergy : ∀ t ∈ Icc 0 T,
      y t + (2 * α) * (∫ s in (0 : ℝ)..t, z s) ≤
        (2 * shift + 1) * (∫ s in (0 : ℝ)..t, y s) + ∫ s in (0 : ℝ)..t, q s := by
    intro t ht
    have hi := Yau.LeafProofs.L16Aux.finitePrimitive_energy_identity hT hrhs hcPrim ⟨le_rfl, hT.le⟩ ht
    rw [hc0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hi
    have hpair := Yau.LeafProofs.L16Aux.finitePrimitive_energy_pairing_intervalIntegrable
      hT hrhs hcPrim ⟨le_rfl, hT.le⟩ ht
    have hyi : IntervalIntegrable y volume 0 t :=
      (hy.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hzi : IntervalIntegrable z volume 0 t :=
      (hz.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hqit : IntervalIntegrable q volume 0 t := hqi.mono_set
      (by simpa only [uIcc_of_le hT.le, uIcc_of_le ht.1] using (Icc_subset_Icc le_rfl ht.2))
    have hInt := intervalIntegral.integral_mono_on ht.1
      ((hpair.const_mul 2).add (hzi.const_mul (2 * α)))
      ((hyi.const_mul (2 * shift + 1)).add hqit)
      (fun s hs => variationalGalerkin_pointwise_energy j e he (B s) (F s) (c s)
        (hGard s ⟨hs.1, hs.2.trans ht.2⟩ _))
    rw [intervalIntegral.integral_add (hpair.const_mul 2) (hzi.const_mul (2 * α)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hyi.const_mul (2 * shift + 1)) hqit,
      intervalIntegral.integral_const_mul, ← hi] at hInt
    exact hInt
  have hbound := coercive_scalar_uniform_bound hT (by positivity : 0 < 2 * α)
    (by positivity : 0 < 2 * shift + 1) hy hz
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _) hqi (fun _ => sq_nonneg _) henergy
  simpa only [y, z, q, ← variationalReconstruction_norm_sq j e he,
    intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo] using hbound

end Yau.F04Proof
