import Yau.Proofs.F04VariationalTime
import Yau.LeafProofs.L16LionsMovingTest

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.MassTargetStatements Yau.LeafProofs.L16LionsMovingTest
variable {n : ℕ} {M : ComplexManifold n}

/-- Native moving-test transport holds for the registered solution's own
 supplied continuous pivot trace and both original closed time endpoints. -/
theorem variationalSolution_moving_test
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure M.Carrier) (O : Set M.Carrier) {T : ℝ} (hT : 0 < T)
    (j : V →L[ℝ] FixedPivot μ O) (hj : ‖j‖ ≤ 1)
    (B : ℝ → V →L[ℝ] EnergyDual V) (f : ℝ → FixedPivot μ O)
    (U : ℝ → V) (R : ℝ → EnergyDual V) (a : ℝ → FixedPivot μ O)
    (hSol : VariationalSolution μ O T j B f U R a) :
    ∀ Φ : ℝ → V, ContDiff ℝ 1 Φ → ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      inner ℝ (a t) (j (Φ t)) - inner ℝ (a s) (j (Φ s)) =
        ∫ q in s..t, R q (Φ q) + inner ℝ (j (U q)) (j (deriv Φ q)) := by
  have hw := variationalSolution_weak_time μ O hT j B f U R a hSol
  rcases hSol with ⟨hU, hR, ha, _ha0, hae, _hscalar, _hEq⟩
  obtain ⟨v, hv, hve, _hChain, hMoving⟩ := hilbert_time_trace_moving_test j hj hT hU hR hw
  have hAE : v =ᵐ[volume.restrict (Ioo 0 T)] a := by
    filter_upwards [hve, hae] with t hvt hat
    exact hvt.symm.trans hat.symm
  rw [restrict_Ioo_eq_restrict_Icc] at hAE
  have hIdent := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hAE hv ha
  intro Φ hΦ s hs t ht
  have hm := hMoving Φ hΦ s hs t ht
  rw [hIdent ht, hIdent hs] at hm
  exact hm

end Yau.F04Proof
