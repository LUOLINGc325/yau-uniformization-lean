import Yau.Proofs.C03RayleighBasic

/-! Unit vectors attaining the frozen infimum and supremum are genuine eigenvectors. -/
noncomputable section
open scoped Matrix ComplexOrder Topology
open Set
namespace Yau.Proofs.C03Aux.Rayleigh
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem unit_sphere_nonempty (hn : 1 ≤ n) :
    (Metric.sphere (0 : ComplexVector n) 1).Nonempty := by
  refine ⟨stdVec ⟨0, Nat.zero_lt_of_lt hn⟩, ?_⟩
  simp [stdVec, EuclideanSpace.single]

theorem exists_unit_min_eigenvector (hn : 1 ≤ n) (H : Herm n) (hH : H.IsHermitian) :
    ∃ e : ComplexVector n, ‖e‖ = 1 ∧
      operator H e = (relMinEigenvalue (1 : Herm n) H : ℂ) • e := by
  obtain ⟨e, he, hmin⟩ := (isCompact_sphere (0 : ComplexVector n) 1).exists_isMinOn
    (unit_sphere_nonempty hn) (operator H).reApplyInnerSelf_continuous.continuousOn
  have hnorm : ‖e‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using he
  have hne : e ≠ 0 := by intro hz; simp [hz] at hnorm
  have heig := (operator_selfAdjoint H hH).hasEigenvector_of_isMinOn hne
    (by simpa only [hnorm] using hmin)
  refine ⟨e, hnorm, ?_⟩
  rw [relMin_eq_iInf]
  exact Module.End.mem_eigenspace_iff.mp heig.1

theorem exists_unit_max_eigenvector (hn : 1 ≤ n) (H : Herm n) (hH : H.IsHermitian) :
    ∃ e : ComplexVector n, ‖e‖ = 1 ∧
      operator H e = (relMaxEigenvalue (1 : Herm n) H : ℂ) • e := by
  obtain ⟨e, he, hmax⟩ := (isCompact_sphere (0 : ComplexVector n) 1).exists_isMaxOn
    (unit_sphere_nonempty hn) (operator H).reApplyInnerSelf_continuous.continuousOn
  have hnorm : ‖e‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using he
  have hne : e ≠ 0 := by intro hz; simp [hz] at hnorm
  have heig := (operator_selfAdjoint H hH).hasEigenvector_of_isMaxOn hne
    (by simpa only [hnorm] using hmax)
  refine ⟨e, hnorm, ?_⟩
  rw [relMax_eq_iSup]
  exact Module.End.mem_eigenspace_iff.mp heig.1

theorem quadratic_of_unit_eigenvector (H : Herm n) (e : ComplexVector n) (lam : ℝ)
    (he : ‖e‖ = 1) (hlam : operator H e = (lam : ℂ) • e) : quadratic H e = lam := by
  rw [quadratic_eq_inner, hlam, inner_smul_right]
  have hi : inner ℂ e e = 1 := by simp [inner_self_eq_norm_sq_to_K, he]
  rw [hi]
  simp

theorem relMin_pos (hn : 1 ≤ n) (H : Herm n) (hH : H.PosDef) :
    0 < relMinEigenvalue (1 : Herm n) H := by
  obtain ⟨e, he, hlam⟩ := exists_unit_min_eigenvector hn H hH.isHermitian
  have hne : e ≠ 0 := by intro hz; simp [hz] at he
  have hp := quadratic_pos H hH e hne
  rwa [quadratic_of_unit_eigenvector H e _ he hlam] at hp

theorem relMin_le_relMax (hn : 1 ≤ n) (H : Herm n) :
    relMinEigenvalue (1 : Herm n) H ≤ relMaxEigenvalue (1 : Herm n) H := by
  obtain ⟨e, he⟩ := unit_sphere_nonempty hn
  have hnorm : ‖e‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using he
  have hne : e ≠ 0 := by intro hz; simp [hz] at hnorm
  exact (rayleigh_bounds H e hne).1.trans (rayleigh_bounds H e hne).2

theorem relMax_pos (hn : 1 ≤ n) (H : Herm n) (hH : H.PosDef) :
    0 < relMaxEigenvalue (1 : Herm n) H :=
  (relMin_pos hn H hH).trans_le (relMin_le_relMax hn H)

theorem lower_bound_relMin (hn : 1 ≤ n) (H : Herm n) (hH : H.PosDef)
    (c : ℝ) (hc : HermLE ((c : ℂ) • (1 : Herm n)) H) :
    c ≤ relMinEigenvalue (1 : Herm n) H := by
  obtain ⟨e, he, hlam⟩ := exists_unit_min_eigenvector hn H hH.isHermitian
  have hnonneg := (Complex.nonneg_iff.mp (hc.dotProduct_mulVec_nonneg (WithLp.ofLp e))).1
  have hform : quadratic H e - c * quadratic (1 : Herm n) e ≥ 0 := by
    simpa only [quadratic, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hnonneg
  rw [quadratic_of_unit_eigenvector H e _ he hlam, quadratic_one, he] at hform
  nlinarith

end Yau.Proofs.C03Aux.Rayleigh
