import Yau.Proofs.F03CompactTestFunctional
import Yau.LeafProofs.L16WeakToClassical

/-! Genuine compact smooth interior tests separate continuous cylinder values. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Yau.Parabolic LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- All genuine compact smooth tests in the actual interior separate C(K)
when that interior is dense in K. No test-density assumption is an inlet. -/
theorem compactTestFunctional_separates {n : ℕ} (K : Set (Point n))
    [CompactSpace K] [IsFiniteMeasure (volume.comap ((↑) : K → Point n))]
    (hK : IsCompact K) (hreg : K = closure (interior K)) (q : C(K,ℝ))
    (hPair : ∀ (φ : Point n → ℝ) (hφ : Test (interior K) φ),
      compactTestFunctional K (volume.comap ((↑) : K → Point n))
        (compactContinuousRestriction K φ hφ.1.continuous.continuousOn) q = 0) : q = 0 := by
  classical
  by_cases hne : Nonempty K
  · have : Nonempty K := hne
    have hclosed : IsClosed K := by rw [hreg]; exact isClosed_closure
    obtain ⟨F,hF⟩ := q.exists_extension' hclosed.isClosedEmbedding_subtypeVal
    have hRestr : compactContinuousRestriction K F F.continuous.continuousOn = q := by
      ext p
      exact congrFun hF p
    have hIC : IsCompact (closure (interior K)) := by rw [← hreg]; exact hK
    have hFL : MemLp F 2 (volume.restrict (interior K)) :=
      continuous_memLp_two_relcompact hIC F.continuous
    have hZero : F =ᵐ[volume.restrict (interior K)] (fun _ => (0 : ℝ)) := by
      apply ae_eq_of_test_integrals_eq isOpen_interior hFL MemLp.zero'
      intro φ hφ
      have hcφ : ContinuousOn φ K := hφ.1.continuous.continuousOn
      have hp := hPair φ hφ
      rw [← hRestr] at hp
      rw [compactTestFunctional_restrict_apply (volume : Measure (Point n)) K hclosed.measurableSet
        φ F hcφ F.continuous.continuousOn] at hp
      have hInt : (∫ p in K, F p * φ p) = ∫ p in interior K, F p * φ p := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hclosed.measurableSet interior_subset
        intro p hp
        rw [image_eq_zero_of_notMem_tsupport (fun hs => hp.2 (hφ.2.2 hs)),mul_zero]
      simpa only [zero_mul,integral_zero,← hInt] using hp
    have hEvery : EqOn F (fun _ => (0 : ℝ)) (interior K) :=
      Measure.eqOn_open_of_ae_eq hZero isOpen_interior F.continuous.continuousOn continuousOn_const
    have hClosure : closure (interior K) ⊆ {p : Point n | F p = 0} :=
      closure_minimal hEvery (isClosed_eq F.continuous continuous_const)
    ext p
    have hp : (p : Point n) ∈ closure (interior K) := by rw [← hreg]; exact p.property
    exact (congrFun hF p).symm.trans (hClosure hp)
  · ext p
    exact (hne ⟨p⟩).elim

end Yau.Proofs.F03Aux
