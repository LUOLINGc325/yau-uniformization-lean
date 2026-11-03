import Yau.LeafProofs.L16WeakWordBootstrap
import Yau.LeafProofs.L16LocalWeakEvolution

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem localEnergy_homogeneous_extended_base_state {n : ℕ}
    {O : Set (Space n)} {l r lam upper : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    (hEll : Elliptic (O ×ˢ Set.Ioo l r) a lam upper)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {W : Set (Point n)} (hW : IsOpen W) (hWC : IsCompact (closure W))
    (hWQ : closure W ⊆ O ×ˢ Set.Ioo l r) :
    ∃ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (C : ℝ),
      0 < C ∧ ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      (∀ j, ContDiff ℝ ∞ (fun p => c p j) ∧ HasCompactSupport (fun p => c p j)) ∧
      (∀ p, ‖A p‖ ≤ C) ∧
      (∀ i h p, ‖spatialDifferenceQuotient A (Yau.realVec i) h p‖ ≤ C) ∧
      (∀ j p, |c p j| ≤ C) ∧
      (∀ j i h p, |spatialDifferenceQuotient (fun q => c q j) (Yau.realVec i) h p| ≤ C) ∧
      Elliptic W A lam upper ∧
      WeakSpatialWordState W A c 0 (initialWeakWordFamily u G) := by
  let Q : Set (Point n) := O ×ˢ Set.Ioo l r
  have hQ : IsOpen Q := hO.prod isOpen_Ioo
  have hWSub : W ⊆ Q := subset_closure.trans hWQ
  obtain ⟨hw,hG⟩ := localEnergy_memLp_on_compact hO hE hWC hWQ
  have hwW : MemLp u 2 (volume.restrict W) :=
    hw.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have hGW (j : Yau.RIdx n) : MemLp (fun p => G p j) 2 (volume.restrict W) :=
    (hG j).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  obtain ⟨A,c,C,hC,hA,hcA,hc,hAgree,hAVal,hADq,hCVal,hCDq⟩ :=
    exists_compact_coefficient_extensions hQ hWC hWQ hSmooth
  have hAEq (p : Point n) (hp : p ∈ W) : A p = a p :=
    (hAgree p (subset_closure hp)).1.eq_of_nhds
  have hCEq (p : Point n) (hp : p ∈ W) (j : Yau.RIdx n) : c p j = energyDrift a b p j :=
    ((hAgree p (subset_closure hp)).2 j).eq_of_nhds
  have hPNew (q : Yau.RIdx n) : MemLp (fun p => energyFlux A G p q) 2 (volume.restrict W) := by
    apply memLp_finsetSum Finset.univ
    intro j _
    exact continuous_bounded_mul_memLp (C := C)
      ((matrixEntryCLM q j).continuous.comp hA.continuous)
      (fun p => (frobenius_entry_abs_le (A p) q j).trans (hAVal p)) (hGW j)
  have hRNew : MemLp (fun p => ∑ j, c p j*G p j) 2 (volume.restrict W) :=
    memLp_finsetSum Finset.univ (fun j _ =>
      continuous_bounded_mul_memLp (hc j).1.continuous (hCVal j) (hGW j))
  have hPNewOld (q : Yau.RIdx n) :
      (fun p => energyFlux A G p q) =ᵐ[volume.restrict W] (fun p => energyFlux a G p q) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with p hp
    unfold energyFlux
    rw [hAEq p hp]
  have hRNewOld : (fun p => ∑ j, c p j*G p j) =ᵐ[volume.restrict W]
      (fun p => ∑ j, energyDrift a b p j*G p j) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with p hp
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun z => z*G p j) (hCEq p hp j))
  have hPOld (q : Yau.RIdx n) : MemLp (fun p => energyFlux a G p q) 2 (volume.restrict W) :=
    (memLp_congr_ae (hPNewOld q)).mp (hPNew q)
  have hROld : MemLp (fun p => ∑ j, energyDrift a b p j*G p j) 2 (volume.restrict W) :=
    (memLp_congr_ae hRNewOld).mp hRNew
  have hEqOld := weakDivergenceEvolutionOn_of_frozen_local hWSub hwW hPOld hROld
    (weakEquation_homogeneous_divergence hEq)
  have hEqNew : WeakDivergenceEvolutionOn W u (energyFlux A G) (fun p => ∑ j, c p j*G p j) :=
    weakDivergenceEvolutionOn_congr_ae hEqOld (Filter.Eventually.of_forall (fun _ => rfl))
      (fun q => (hPNewOld q).symm) hRNewOld.symm
  have hWGW : WeakGradientOn W u G :=
    weakGradientOn_mono ((weakGradientOn_prod_iff O (Set.Ioo l r) u G).2 hE.1) hWSub
  have hEllW : Elliptic W A lam upper := by
    refine ⟨hEll.1,hEll.2.1,?_⟩
    intro p hp
    rw [hAEq p hp]
    exact hEll.2.2 p (hWSub hp)
  exact ⟨A,c,C,hC,hA,hcA,hc,hAVal,hADq,hCVal,hCDq,hEllW,
    initialWeakWordFamily_state hwW hGW hWGW hEqNew⟩

theorem localEnergy_homogeneous_finite_spatial_weak_jets {n : ℕ}
    {O : Set (Space n)} {l r lam upper : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    (hEll : Elliptic (O ×ˢ Set.Ioo l r) a lam upper)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    (k : ℕ) {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVQ : closure V ⊆ O ×ˢ Set.Ioo l r) :
    ∃ U : List (Yau.RIdx n) → Point n → ℝ,
      U [] = u ∧ (∀ j, U [j] = fun p => G p j) ∧
      (∀ w, w.length ≤ k+1 → MemLp (U w) 2 (volume.restrict V)) ∧
      (∀ w, w.length ≤ k → WeakGradientOn V (U w) (fun p i => U (i::w) p)) := by
  have hQ : IsOpen (O ×ˢ Set.Ioo l r) := hO.prod isOpen_Ioo
  obtain ⟨W,hW,hVW,hWQ,hWC⟩ := exists_open_between_and_isCompact_closure hVC hQ hVQ
  obtain ⟨A,c,C,hC,hA,hcA,hc,hAVal,hADq,hCVal,hCDq,hEllW,hBase⟩ :=
    localEnergy_homogeneous_extended_base_state hO hSmooth hEll hE hEq hW hWC hWQ
  obtain ⟨U,hU0,hState⟩ := exists_finite_weakSpatialWordState hW hC.le hEllW
    hA hcA (fun j => (hc j).1) (fun j => (hc j).2) hAVal hCVal hADq hCDq
    (initialWeakWordFamily u G) hBase k V hV hVC hVW
  exact ⟨U,hU0 [] (by simp),fun j => hU0 [j] (by simp),hState.1,hState.2.1⟩

end Yau.LeafProofs.L16Aux
