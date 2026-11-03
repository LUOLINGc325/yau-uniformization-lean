import Yau.Proofs.C05NormalizedScalarTimeEvolutionScaling
import Yau.Proofs.C05ThirdScalarTime

/-! The original first, second and third time derivatives equal the intrinsic sources of one constant rescaling. -/
noncomputable section
open scoped Manifold Topology ContDiff
namespace Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau Yau.Blueprint Yau.Proofs.C04Aux Yau.Proofs.C05Aux Yau.Proofs.C05ThirdScalarTimeAux Set
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalar_time_slices_smooth (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (t : ℝ) (ht : 0 < t) :
    SmoothFn (scalarCurvature (h t)) ∧
    SmoothFn (fun y => deriv (fun s => scalarCurvature (h s) y) t) ∧
    SmoothFn (fun y => deriv (fun s => deriv (fun r => scalarCurvature (h r) y) s) t) := by
  have hu := localizedFlow_scalar_smoothSpaceTime X o h U P rho hf
  have hut := smoothSpaceTime_timeDeriv isOpen_Ioi hu
  have hutt := smoothSpaceTime_timeDeriv isOpen_Ioi hut
  exact ⟨spaceSlice_smoothFn hu ht, spaceSlice_smoothFn hut ht, spaceSlice_smoothFn hutt ht⟩

theorem normalized_scalar_first_eq_source (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (x : Pt X) :
    deriv (fun s => scalarCurvature (h s) x) t / R^2 =
      scalarTimeSource1 (scaleField R hR (h t)) x := by
  have hs := (scalar_time_slices_smooth o h U P rho hf t ht).1
  have hsc : scalarCurvature (scaleField R hR (h t)) =
      (fun y => R⁻¹ * scalarCurvature (h t) y) := by
    funext y
    exact scalar_scaleField R hR (h t) y
  rw [scalar_time_evolution o h U P rho hf x ht,
    scalarTimeSource1, scalarHarnackSource, hsc, laplacian_scaleField,
    laplacian_const_mul _ _ hs, ricciNormSq_scaleField]
  field_simp [hR.ne']
  ring

theorem source1_scaled_function (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (t R : ℝ) (ht : 0 < t) (hR : 0 < R) :
    scalarTimeSource1 (scaleField R hR (h t)) =
      (fun y => R⁻¹ ^ 2 * deriv (fun s => scalarCurvature (h s) y) t) := by
  funext y
  rw [← normalized_scalar_first_eq_source o h U P rho hf t R ht hR y]
  field_simp [hR.ne']

theorem normalized_scalar_second_eq_source (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (x : Pt X) :
    deriv (fun s => deriv (fun r => scalarCurvature (h r) x) s) t / R^3 =
      scalarTimeSource2 (scaleField R hR (h t)) x := by
  obtain ⟨hs, hs1, _⟩ := scalar_time_slices_smooth o h U P rho hf t ht
  have hsc : scalarCurvature (scaleField R hR (h t)) =
      (fun y => R⁻¹ * scalarCurvature (h t) y) := by
    funext y
    exact scalar_scaleField R hR (h t) y
  rw [(scalar_second_hasDerivAt o h U P rho hf x ht).deriv,
    scalarTimeSource2, source1_scaled_function o h U P rho hf t R ht hR,
    hsc, laplacian_scaleField, laplacian_const_mul _ _ hs1,
    ricciLeviPairing_scaled_function R hR (h t) _ hs,
    ricciCube_scaleField]
  field_simp [hR.ne']

theorem source2_scaled_function (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (t R : ℝ) (ht : 0 < t) (hR : 0 < R) :
    scalarTimeSource2 (scaleField R hR (h t)) =
      (fun y => R⁻¹ ^ 3 * deriv
        (fun s => deriv (fun r => scalarCurvature (h r) y) s) t) := by
  funext y
  rw [← normalized_scalar_second_eq_source o h U P rho hf t R ht hR y]
  field_simp [hR.ne']

theorem normalized_scalar_third_eq_source (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (x : Pt X) :
    deriv (fun s => deriv (fun r => deriv (fun q => scalarCurvature (h q) x) r) s) t / R^4 =
      scalarTimeSource3 (scaleField R hR (h t)) x := by
  obtain ⟨hs, hs1, hs2⟩ := scalar_time_slices_smooth o h U P rho hf t ht
  rw [(scalar_third_hasDerivAt_polynomial o h U P rho hf x ht).deriv,
    scalarTimeSource3, source2_scaled_function o h U P rho hf t R ht hR,
    source1_scaled_function o h U P rho hf t R ht hR,
    laplacian_scaleField, laplacian_const_mul _ _ hs2,
    ricciLeviPairing_scaled_function R hR (h t) _ hs1,
    ricciSquareLevi_scaleField R hR (h t) hs,
    leviScalarSquare_scaleField R hR (h t) hs,
    ricciQuartic_scaleField]
  field_simp [hR.ne']

end Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
