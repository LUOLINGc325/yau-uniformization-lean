import Yau.Proofs.F04WeakTimeBinding
import spec.WORKPACKAGES.STATEMENTS.MASS.EnergyBindings

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.MassTargetStatements Yau.LeafProofs.L16HilbertTimeRegularization
  Yau.LeafProofs.L16LionsTimeTrace

variable {n : ℕ} {M : ComplexManifold n}

theorem variationalSolution_weak_time
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure M.Carrier) (O : Set M.Carrier) {T : ℝ} (hT : 0 < T)
    (j : V →L[ℝ] FixedPivot μ O) (B : ℝ → V →L[ℝ] EnergyDual V)
    (f : ℝ → FixedPivot μ O) (U : ℝ → V) (R : ℝ → EnergyDual V)
    (a : ℝ → FixedPivot μ O) (hsol : VariationalSolution μ O T j B f U R a) :
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, η t • R t) := by
  rcases hsol with ⟨hU, hR, _ha, _h0, hae, hw, _hEq⟩
  exact hilbert_weak_time_of_scalar_tests j hT hU hR a (hae.mono (fun _ h => h.symm)) hw

/-- The registered variational solution's own supplied closed-time trace
satisfies the exact energy chain; no replacement trace is used in the result. -/
theorem variationalSolution_time_chain
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure M.Carrier) (O : Set M.Carrier) {T : ℝ} (hT : 0 < T)
    (j : V →L[ℝ] FixedPivot μ O) (hj : ‖j‖ ≤ 1)
    (B : ℝ → V →L[ℝ] EnergyDual V) (f : ℝ → FixedPivot μ O)
    (U : ℝ → V) (R : ℝ → EnergyDual V) (a : ℝ → FixedPivot μ O)
    (hsol : VariationalSolution μ O T j B f U R a) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      ‖a t‖ ^ 2 - ‖a s‖ ^ 2 = 2 * ∫ q in s..t, R q (U q) := by
  have hw := variationalSolution_weak_time μ O hT j B f U R a hsol
  rcases hsol with ⟨hU, hR, ha, _h0, hae, _hw, _hEq⟩
  obtain ⟨b, hb, hbae, hchain⟩ := hilbert_time_trace_chain j hj hT hU hR hw
  have hba : b =ᵐ[volume.restrict (Ioo 0 T)] a := by
    filter_upwards [hbae, hae] with t hbt hat
    exact hbt.symm.trans hat.symm
  rw [restrict_Ioo_eq_restrict_Icc] at hba
  have heq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hba hb ha
  intro s hs t ht
  rw [← heq hs, ← heq ht]
  exact hchain s hs t ht

end Yau.F04Proof
