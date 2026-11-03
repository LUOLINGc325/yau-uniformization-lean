import Yau.Proofs.P06SpectralRationalResolvent

noncomputable section
open Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux
open ComplexHilbert Yau.LeafProofs.L19Aux
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : H →ₗ.[ℝ] H) (hd : Dense (T.domain : Set H)) (hself : T.adjoint = T)
  (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u))

def normalizedResolventEuler (t : ℝ) (ht : 0 < t) (j : ℕ) : H →L[ℝ] H :=
  normalizedResolvent T hd hself hp (t / scalarEulerCount j)
    (div_pos ht (scalarEulerCount_cast_pos j)) ^ scalarEulerCount j

variable (R : H →L[ℝ] H) (hRs : R.IsSymmetric) (hRp : ∀ x, 0 ≤ inner ℝ (R x) x)
  (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R)
  (hR : R = positiveResolvent T hd hself hp 1 zero_lt_one)

include hRs hRp hRb hRi hR

theorem normalizedResolventEuler_complexify (t : ℝ) (ht : 0 < t) (j : ℕ) :
    complexify (normalizedResolventEuler T hd hself hp t ht j) =
      cfc (scalarEulerPowerMultiplier t j) (complexify R) := by
  rw [normalizedResolventEuler, complexify_pow,
    normalizedResolvent_complexify_eq_cfc T hd hself hp R hRs hRp hRb hRi hR,
    ← cfc_pow (scalarEulerMultiplier (t / scalarEulerCount j)) (scalarEulerCount j)
      (complexify R)
      ((scalarEulerMultiplier_continuousOn (div_pos ht (scalarEulerCount_cast_pos j))).mono
        (Spectral.complexResolvent_spectrum R hRs hRp hRb hRi))
      (complexify_selfAdjoint R hRs)]
  rfl

/-- The original implicit resolvents converge in operator norm to the same
CFC family. No scalar positivity property is imported into the form cone. -/
theorem normalizedResolventEuler_complex_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun j => complexify (normalizedResolventEuler T hd hself hp t ht j)) atTop
      (𝓝 (Spectral.complexHeat R hRs hRp hRb hRi t)) := by
  let B := complexify R
  have hB : IsSelfAdjoint B := complexify_selfAdjoint R hRs
  have hσ : spectrum ℝ B ⊆ Set.Icc 0 1 :=
    Spectral.complexResolvent_spectrum R hRs hRp hRb hRi
  let π : C(spectrum ℝ B, Set.Icc (0 : ℝ) 1) :=
    ⟨fun s => ⟨s, hσ s.property⟩, continuous_subtype_val.subtype_mk _⟩
  let A := (cfcL (R := ℝ) hB).comp (ContinuousMap.compCLM ℝ ℝ π)
  have heq (j : ℕ) : A
      (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarEulerPowerMultiplier t j s,
        (scalarEulerPowerMultiplier_continuousOn ht j).domRestrict⟩ :
          C(Set.Icc (0 : ℝ) 1, ℝ)) =
        complexify (normalizedResolventEuler T hd hself hp t ht j) := by
    rw [normalizedResolventEuler_complexify T hd hself hp R hRs hRp hRb hRi hR,
      cfc_eq_cfcL hB ((scalarEulerPowerMultiplier_continuousOn ht j).mono hσ)]
    rfl
  have hlim : A
      (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarHeatMultiplier t s,
        (scalarHeatMultiplier_continuous ht).comp continuous_subtype_val⟩ :
          C(Set.Icc (0 : ℝ) 1, ℝ)) = Spectral.complexHeat R hRs hRp hRb hRi t := by
    rw [Spectral.complexHeat_of_pos R hRs hRp hRb hRi ht]
    change _ = cfc (scalarHeatMultiplier t) B
    rw [cfc_eq_cfcL hB (scalarHeatMultiplier_continuous ht).continuousOn]
    rfl
  have h := A.continuous.continuousAt.tendsto.comp (scalarEulerPowerMultiplier_uniform ht)
  simpa only [Function.comp_def, heq, hlim] using h

theorem normalizedResolventEuler_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (normalizedResolventEuler T hd hself hp t ht) atTop
      (𝓝 (Spectral.realHeat R hRs hRp hRb hRi t)) := by
  have h := Spectral.realRestrictionCLM.continuous.continuousAt.tendsto.comp
    (normalizedResolventEuler_complex_tendsto T hd hself hp R hRs hRp hRb hRi hR t ht)
  simpa only [Function.comp_def, realRestriction_complexify, Spectral.realRestriction_heat] using h

theorem normalizedResolventEuler_apply_tendsto (t : ℝ) (ht : 0 < t) (f : H) :
    Tendsto (fun j => normalizedResolventEuler T hd hself hp t ht j f) atTop
      (𝓝 (Spectral.realHeat R hRs hRp hRb hRi t f)) :=
  (ContinuousLinearMap.apply ℝ H f).continuous.continuousAt.tendsto.comp
    (normalizedResolventEuler_tendsto T hd hself hp R hRs hRp hRb hRi hR t ht)

end Yau.NodeProofs.P06Aux
