import Yau.Proofs.E01JohnCone
import Yau.Proofs.E01SmallCoefficients
import Yau.Proofs.E01HomogeneousFeasible

/-! Exact unit contacts with arbitrarily small positive coefficients. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem exists_small_unit_contact_identity
    (v : ComplexVector n → EReal)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
        (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
      (∀ i, 0 < α i ∧ α i ≤ ε ∧ v (η i) = 1 ∧
        ellipsoidQuadratic (1 : Herm n) (η i) = 1) ∧
      (∑ i, (α i : ℂ) • contactRankOne (η i)) = 1 ∧ ∑ i, α i = n := by
  obtain ⟨m, η, α, hη, hmatrix, hsum⟩ := exists_finite_unit_contact_identity v hv hlower hmax
  obtain ⟨m', index, β, hβ, hmatrix', hsum'⟩ :=
    split_positive_conic_coefficients (fun i => contactRankOne (η i)) α
      (fun i => (hη i).1) (n : ℝ) hsum ε hε
  have hmatrixReal : (∑ i, α i • contactRankOne (η i)) = (1 : Herm n) := by
    simpa only [Complex.coe_smul] using hmatrix
  have hmatrixβ : (∑ j, (β j : ℂ) • contactRankOne (η (index j))) = (1 : Herm n) := by
    simpa only [Complex.coe_smul] using hmatrix'.trans hmatrixReal
  refine ⟨m', (fun j => η (index j)), β, ?_, hmatrixβ, hsum'⟩
  intro j
  refine ⟨(hβ j).1, (hβ j).2, (hη (index j)).2.2, ?_⟩
  rw [ellipsoidQuadratic_one, unitContactSet_norm (hη (index j)).2]
  norm_num

theorem small_unit_contacts_of_homogeneous_max
    (v : ComplexVector n → EReal)
    (hhom : ∀ r : ℝ, 0 < r → ∀ η : ComplexVector n,
      v ((r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v η)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hI : ∀ η, (ellipsoidQuadratic (1 : Herm n) η : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
      (∀ i, 0 < α i ∧ α i ≤ ε ∧ v (η i) = 1 ∧
        ellipsoidQuadratic (1 : Herm n) (η i) = 1) ∧
      (∑ i, (α i : ℂ) • contactRankOne (η i)) = 1 ∧ ∑ i, α i = n := by
  have hzero : (0 : EReal) ≤ v 0 := by
    simpa only [ellipsoidQuadratic_zero_vector, EReal.coe_zero] using hI 0
  have hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η := by
    intro η hη
    have hn : ‖η‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hη
    simpa only [ellipsoidQuadratic_one, hn, one_pow, EReal.coe_one] using hI η
  exact exists_small_unit_contact_identity v hv hlower
    (fun D hD hDv => hmax D hD (homogeneous_minorant_of_sphere v hzero hhom D hDv)) ε hε

end Yau.NodeProofs.E01Aux
