import Yau.Proofs.F04CoefficientBounds
import Yau.Proofs.F04ClassicalDivergence
import Yau.LeafProofs.L16CoefficientForcing

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- The actual coefficient bounds on a compact buffer produce the true L2
 flux and computed divergence-drift source from the actual L2 gradient. -/
theorem compact_buffer_weak_fields_memLp {n : ℕ} {O V : Set (Space n)}
    (hO : IsOpen O) (hV : IsOpen V) (hVC : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {S s : ℝ} (hs : 0 < s) (hsS : s ≤ S)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    {G : Point n → Yau.RIdx n → ℝ}
    (hG : ∀ i, MemLp (fun p => G p i) 2 (productVolume V (Ioo 0 s))) :
    (∀ i, MemLp (fun p => energyFlux a G p i) 2 (productVolume V (Ioo 0 s))) ∧
      MemLp (fun p => ∑ i, energyDrift a b p i * G p i) 2 (productVolume V (Ioo 0 s)) := by
  let Q : Set (Point n) := V ×ˢ Ioo 0 s
  have hQ : IsOpen Q := hV.prod isOpen_Ioo
  have hSub : Q ⊆ O ×ˢ Icc 0 S := fun p hp =>
    ⟨hVO (subset_closure hp.1), hp.2.1.le, hp.2.2.le.trans hsS⟩
  have hAS : ContDiffOn ℝ ∞ a Q := hSmooth.1.mono hSub
  have hBS : ∀ i, ContDiffOn ℝ ∞ (fun p => energyDrift a b p i) Q :=
    energyDrift_smooth hQ ⟨hAS, fun i => (hSmooth.2 i).mono hSub⟩
  have hKS : closure V ×ˢ Icc (0 : ℝ) s ⊆ O ×ˢ Icc 0 S :=
    fun p hp => ⟨hVO hp.1, hp.2.1, hp.2.2.trans hsS⟩
  obtain ⟨C, hC⟩ := (hVC.prod isCompact_Icc).exists_bound_of_continuousOn
    (hSmooth.1.continuousOn.mono hKS)
  obtain ⟨D, hD, hDb⟩ := compact_buffer_drift_bound hV hVC
    ⟨hSmooth.1.mono hKS, fun i => (hSmooth.2 i).mono hKS⟩
  have hMul (c : Point n → ℝ) (hc : AEStronglyMeasurable c (productVolume V (Ioo 0 s)))
      (A : ℝ) (hA : ∀ p ∈ Q, |c p| ≤ A) (i : Yau.RIdx n) :
      MemLp (fun p => c p * G p i) 2 (productVolume V (Ioo 0 s)) := by
    have hTop : MemLp c (⊤ : ENNReal) (productVolume V (Ioo 0 s)) := by
      apply memLp_top_of_bound hc A
      rw [productVolume_eq_restrict]
      filter_upwards [ae_restrict_mem hQ.measurableSet] with p hp
      simpa only [Real.norm_eq_abs] using hA p hp
    exact hTop.mul (hG i)
  constructor
  · intro i
    apply memLp_finsetSum Finset.univ
    intro j _
    apply hMul (fun p => a p i j)
      (by
        rw [productVolume_eq_restrict]
        exact ((matrixEntryCLM i j).continuous.comp_continuousOn hAS.continuousOn).aestronglyMeasurable hQ.measurableSet)
      C _ j
    intro p hp
    exact (frobenius_entry_abs_le (a p) i j).trans (hC p ⟨subset_closure hp.1, Ioo_subset_Icc_self hp.2⟩)
  · apply memLp_finsetSum Finset.univ
    intro i _
    apply hMul (fun p => energyDrift a b p i)
      (by
        rw [productVolume_eq_restrict]
        exact (hBS i).continuousOn.aestronglyMeasurable hQ.measurableSet) D _ i
    intro p hp
    have hOne : (energyDrift a b p i) ^ 2 ≤ D ^ 2 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (energyDrift a b p j)) (Finset.mem_univ i)).trans
        (hDb p hp)
    exact (sq_le_sq₀ (abs_nonneg _) hD.le).mp (by simpa only [sq_abs] using hOne)

end Yau.F04Proof
