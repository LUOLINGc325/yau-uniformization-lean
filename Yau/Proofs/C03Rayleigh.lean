import Yau.Proofs.C03RayleighDual

/-! Natural spectral data and normalized covectors for the original static-distortion proof. -/
noncomputable section
open scoped Matrix ComplexOrder Topology
namespace Yau.Proofs.C03Aux.Rayleigh
open Yau Yau.Blueprint
variable {n : ℕ}

theorem positive_extrema_and_bounds (hn : 1 ≤ n) (H : Herm n) (hH : H.PosDef) :
    0 < relMinEigenvalue (1 : Herm n) H ∧
      relMinEigenvalue (1 : Herm n) H ≤ relMaxEigenvalue (1 : Herm n) H ∧
      ∀ v : ComplexVector n, v ≠ 0 →
        relMinEigenvalue (1 : Herm n) H ≤
          (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re / ‖v‖ ^ 2 ∧
        (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re / ‖v‖ ^ 2 ≤
          relMaxEigenvalue (1 : Herm n) H :=
  ⟨relMin_pos hn H hH, relMin_le_relMax hn H, rayleigh_bounds H⟩

theorem exists_unit_extreme_eigenvectors (hn : 1 ≤ n) (H : Herm n) (hH : H.PosDef) :
    ∃ emin emax : ComplexVector n, ‖emin‖ = 1 ∧ ‖emax‖ = 1 ∧
      WithLp.toLp 2 (H *ᵥ WithLp.ofLp emin) =
        (relMinEigenvalue (1 : Herm n) H : ℂ) • emin ∧
      WithLp.toLp 2 (H *ᵥ WithLp.ofLp emax) =
        (relMaxEigenvalue (1 : Herm n) H : ℂ) • emax := by
  obtain ⟨emin, hmin, hemin⟩ := exists_unit_min_eigenvector hn H hH.isHermitian
  obtain ⟨emax, hmax, hemax⟩ := exists_unit_max_eigenvector hn H hH.isHermitian
  exact ⟨emin, emax, hmin, hmax, hemin, hemax⟩

theorem exists_normalized_extreme_covectors (hn : 1 ≤ n) (H : Herm n) (hH : H.PosDef) :
    ∃ α β : Covector n,
      ‖α‖ = Real.sqrt (relMinEigenvalue (1 : Herm n) H) ∧
      ‖β‖ = Real.sqrt (relMaxEigenvalue (1 : Herm n) H) ∧
      dualNormMat H (WithLp.toLp 2 (fun i => α (stdVec i))) = 1 ∧
      dualNormMat H (WithLp.toLp 2 (fun i => β (stdVec i))) = 1 := by
  obtain ⟨emin, hmin, hemin⟩ := exists_unit_min_eigenvector hn H hH.isHermitian
  obtain ⟨emax, hmax, hemax⟩ := exists_unit_max_eigenvector hn H hH.isHermitian
  exact ⟨normalizedCovector _ emin, normalizedCovector _ emax,
    normalizedCovector_norm _ emin hmin, normalizedCovector_norm _ emax hmax,
    normalizedCovector_dualNorm H hH emin _ hmin (relMin_pos hn H hH) hemin,
    normalizedCovector_dualNorm H hH emax _ hmax (relMax_pos hn H hH) hemax⟩

end Yau.Proofs.C03Aux.Rayleigh
