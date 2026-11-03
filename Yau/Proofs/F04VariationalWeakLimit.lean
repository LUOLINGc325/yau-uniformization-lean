import Yau.Proofs.F04GalerkinUniform
import Yau.Proofs.F04BochnerL2
import Yau.LeafProofs.L16EnergyWeakCompactness
import Yau.LeafProofs.L16HilbertTimeRegularization

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

/-- Actual continuous energy curves with uniform squared time norm have a
 genuine weak Bochner subsequence in the original energy space. -/
theorem variational_continuous_curves_weak_limit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SeparableSpace V] {T C : ℝ}
    (USeq : ℕ → ℝ → V) (hCont : ∀ m, ContinuousOn (USeq m) (Icc 0 T))
    (hEnergy : ∀ m, (∫ t in Ioo 0 T, ‖USeq m t‖ ^ 2) ≤ C) :
    ∃ hMem : ∀ m, MemLp (USeq m) 2 (volume.restrict (Ioo 0 T)),
    ∃ U : Lp V 2 (volume.restrict (Ioo 0 T)), ‖U‖ ^ 2 ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ ℓ : Lp V 2 (volume.restrict (Ioo 0 T)) →L[ℝ] ℝ,
          Tendsto (fun k => ℓ ((hMem (φ k)).toLp (USeq (φ k)))) atTop (𝓝 (ℓ U)) := by
  have hMem (m : ℕ) : MemLp (USeq m) 2 (volume.restrict (Ioo 0 T)) :=
    (Yau.LeafProofs.L16HilbertTimeRegularization.continuousOn_memLp_two (hCont m)).mono_measure
      (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  let classes : ℕ → Lp V 2 (volume.restrict (Ioo 0 T)) := fun m => (hMem m).toLp (USeq m)
  have hBound (m : ℕ) : ‖classes m‖ ^ 2 ≤ C := by
    rw [bochner_l2_norm_sq_integral]
    calc
      _ = ∫ t in Ioo 0 T, ‖USeq m t‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [(hMem m).coeFn_toLp] with t ht
        rw [ht]
      _ ≤ C := hEnergy m
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp V 2 (volume.restrict (Ioo 0 T))) :=
    MeasureTheory.Lp.SecondCountableTopology
  obtain ⟨U, hU, φ, hφ, _hInner, hWeak⟩ :=
    Yau.LeafProofs.L16Aux.exists_strictMono_weak_tendsto_of_norm_sq_le classes C hBound
  exact ⟨hMem, U, hU, φ, hφ, hWeak⟩

end Yau.F04Proof
