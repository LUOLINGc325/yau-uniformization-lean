import Yau.Geometry.HolomorphicBundle
import Yau.Proofs.P03Measure

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem localDomain_isOpen (a : M.Carrier) :
    IsOpen (localDomain (r := r) E a) := by
  exact (continuousOn_extChartAt_symm (I := ComplexModel n) a).isOpen_inter_preimage
    (isOpen_extChartAt_target a) (localTriv (r := r) E a).open_baseSet

def zeroForm (q : ℕ) : NQForm E q := fun _ => ⟨0, by
  intro v i c
  simp⟩

theorem coefficients_zeroForm (q : ℕ) (a : M.Carrier) (z : ComplexVector n)
    (I : Fin q → Fin n) : coefficients (r := r) E (zeroForm E q) a z I = 0 := by
  simp [coefficients, zeroForm]

theorem locallyL2_coefficients_memLp {q : ℕ} (u : NQForm E q)
    (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (I : Fin q → Fin n) (α : Fin r) (K : Set (ComplexVector n))
    (hK : IsCompact K) (hsub : K ⊆ localDomain (r := r) E a) :
    MemLp (fun z => coefficients (r := r) E u a z I α) 2 ((lebesgueC n).restrict K) := by
  have hm := (hu a I α).1.mono_measure (Measure.restrict_mono hsub le_rfl)
  exact memLp_two_of_lintegral_norm_sq_lt_top hm ((hu a I α).2 K hK hsub)

/-- The homogeneous native weak dbar equation gives exactly the scalar test
identities consumed by local Cauchy–Riemann regularity. -/
theorem weakDbar_zero_scalar_tests (u : NQForm E 0)
    (hu : WeakDbar (r := r) E u (zeroForm E 1))
    (a : M.Carrier) (i : Fin n) (α : Fin r) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, coefficients (r := r) E u a z Fin.elim0 α *
      wirtBar ψ z (stdVec i) ∂lebesgueC n) = 0 := by
  have ht := hu.2.2 a (fun _ => i) α ψ hψ hcψ hsψ
  have hidx : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → Fin n) := by
    funext j
    exact Fin.elim0 j
  have hz : (0 : ℂ) = -(∫ z, coefficients (r := r) E u a z Fin.elim0 α *
      wirtBar ψ z (stdVec i) ∂lebesgueC n) := by
    simpa [coefficients_zeroForm, Fin.sum_univ_one, hidx] using ht
  exact neg_eq_zero.mp hz.symm

/-- Keep the genuine local L² information together with the scalar weak-CR
identity; no finite real Bochner integral is used as an integrability premise. -/
theorem weakDbar_zero_local_data (u : NQForm E 0)
    (hu : WeakDbar (r := r) E u (zeroForm E 1)) (a : M.Carrier) (α : Fin r) :
    AEStronglyMeasurable (fun z => coefficients (r := r) E u a z Fin.elim0 α)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) ∧
    (∀ K : Set (ComplexVector n), IsCompact K → K ⊆ localDomain (r := r) E a →
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z Fin.elim0 α‖ ^ 2)
        ∂lebesgueC n) < ⊤) ∧
    ∀ (i : Fin n) (ψ : ComplexVector n → ℂ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ localDomain (r := r) E a →
      (∫ z, coefficients (r := r) E u a z Fin.elim0 α *
        wirtBar ψ z (stdVec i) ∂lebesgueC n) = 0 := by
  exact ⟨(hu.1 a Fin.elim0 α).1, (hu.1 a Fin.elim0 α).2,
    fun i ψ hψ hcψ hsψ => weakDbar_zero_scalar_tests E u hu a i α ψ hψ hcψ hsψ⟩

end Yau.NodeProofs.P03Aux
