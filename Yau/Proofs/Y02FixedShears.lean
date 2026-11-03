import Yau.Proofs.Y02ShearSpanning
import Yau.Proofs.Y02FiniteCoefficientBound

/-! A finite shear list and a fixed linear, uniformly bounded decomposition. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

abbrev DivFreeHom (n m : ℕ) :=
  ↥(homogeneousFields n m ⊓ LinearMap.ker (divergence n))

theorem homogeneousFields_fg (n m : ℕ) : (homogeneousFields n m).FG := by
  have heq : homogeneousFields n m =
      Submodule.pi Set.univ (fun _ : Fin n => homogeneousSubmodule (Fin n) ℂ m) := by
    ext P
    simp [homogeneousFields, Submodule.mem_pi, mem_homogeneousSubmodule]
  rw [heq]
  exact Submodule.fg_pi (fun _ => homogeneousSubmodule_fg (Fin n) ℂ m)

theorem exists_finite_shear_span (n m : ℕ) (hm : 2 ≤ m) :
    ∃ F : Finset (PolyMap n),
      (∀ P ∈ F, P ∈ shearFields n m) ∧
        Submodule.span ℂ (F : Set (PolyMap n)) =
          homogeneousFields n m ⊓ LinearMap.ker (divergence n) := by
  have hfg : (Submodule.span ℂ (shearFields n m)).FG :=
    (homogeneousFields_fg n m).of_le ((shearFields_span_le m).trans inf_le_left)
  obtain ⟨F, hF, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  refine ⟨F, fun P hP => hF hP, ?_⟩
  rw [← hspan, shearFields_span_eq m hm]

theorem exists_fixed_finite_shear_decomposition (n m : ℕ) (hm : 2 ≤ m) :
    ∃ (F : Finset (PolyMap n)) (l v : F → Fin n → ℂ)
        (R : PolyMap n →ₗ[ℂ] (F → ℂ)) (C : ℝ),
      0 ≤ C ∧
      (∀ t, ∑ i, l t i * v t i = 0) ∧
      (∀ P : DivFreeHom n m,
        (∑ t, R P t • shearField (l t) (v t) m) = (P : PolyMap n)) ∧
      (∀ P : PolyMap n, P ∈ homogeneousFields n m →
        (∑ t, ‖R P t‖) ≤ C * P.coeffNorm) := by
  classical
  obtain ⟨F, hF, hspan⟩ := exists_finite_shear_span n m hm
  let K : Submodule ℂ (PolyMap n) := homogeneousFields n m ⊓ LinearMap.ker (divergence n)
  have hfields : ∀ t : F, ∃ l v : Fin n → ℂ,
      (∑ i, l i * v i = 0) ∧ (t : PolyMap n) = shearField l v m := by
    intro t
    exact hF t t.property
  choose l v hlv hfield using hfields
  let f : (F → ℂ) →ₗ[ℂ] PolyMap n :=
    Fintype.linearCombination ℂ (fun t : F => (t : PolyMap n))
  have hrange : LinearMap.range f = K := by
    rw [Fintype.range_linearCombination]
    have heq : Set.range (fun t : F => (t : PolyMap n)) = (F : Set (PolyMap n)) := by
      ext P
      simp
    rw [heq]
    exact hspan
  let fK : (F → ℂ) →ₗ[ℂ] K := f.codRestrict K (fun c => hrange ▸ LinearMap.mem_range_self f c)
  have hsurj : Function.Surjective fK := by
    intro P
    have hP : (P : PolyMap n) ∈ LinearMap.range f := hrange.symm ▸ P.property
    obtain ⟨c, hc⟩ := hP
    exact ⟨c, Subtype.ext hc⟩
  obtain ⟨R, hR⟩ := fK.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  obtain ⟨Rambient, hext⟩ := R.exists_extend
  obtain ⟨C, hC, hbound⟩ := exists_linear_coefficient_bound m Rambient
  refine ⟨F, l, v, Rambient, C, hC, hlv, ?_, hbound⟩
  intro P
  have hextP : Rambient (P : PolyMap n) = R P := LinearMap.congr_fun hext P
  rw [hextP]
  have hsec : fK (R P) = P := LinearMap.congr_fun hR P
  have hsec' : f (R P) = (P : PolyMap n) := congrArg Subtype.val hsec
  rw [Fintype.linearCombination_apply] at hsec'
  simpa only [hfield] using hsec'

/-- The list, all shear directions, the coefficient map and its bound are fixed
before the homogeneous divergence-free field is supplied. -/
theorem exists_fixed_shear_decomposition (n m : ℕ) (hm : 2 ≤ m) :
    ∃ (N : ℕ) (l v : Fin N → Fin n → ℂ)
        (R : PolyMap n →ₗ[ℂ] (Fin N → ℂ)) (C : ℝ),
      0 ≤ C ∧
      (∀ t, ∑ i, l t i * v t i = 0) ∧
      (∀ P : DivFreeHom n m,
        (∑ t, R P t • shearField (l t) (v t) m) = (P : PolyMap n)) ∧
      (∀ P : PolyMap n, P ∈ homogeneousFields n m →
        (∑ t, ‖R P t‖) ≤ C * P.coeffNorm) := by
  classical
  obtain ⟨F, l, v, R, C, hC, hlv, hsynth, hbound⟩ :=
    exists_fixed_finite_shear_decomposition n m hm
  let e := Fintype.equivFin F
  let Rfin : PolyMap n →ₗ[ℂ] (Fin (Fintype.card F) → ℂ) :=
    LinearMap.pi (fun t => (LinearMap.proj (e.symm t)).comp R)
  refine ⟨Fintype.card F, fun t => l (e.symm t), fun t => v (e.symm t), Rfin, C,
    hC, fun t => hlv (e.symm t), ?_, ?_⟩
  · intro P
    change (∑ t, R P (e.symm t) • shearField (l (e.symm t)) (v (e.symm t)) m) = _
    rw [e.symm.sum_comp (fun t => R P t • shearField (l t) (v t) m)]
    exact hsynth P
  · intro P hP
    change (∑ t, ‖R P (e.symm t)‖) ≤ _
    rw [e.symm.sum_comp (fun t => ‖R P t‖)]
    exact hbound P hP

end Yau.Proofs.Y02Aux
