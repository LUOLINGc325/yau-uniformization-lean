import Yau.Proofs.F04CoefficientBounds
import Yau.Proofs.F04ClassicalWeakGradient
import Yau.LeafProofs.L16ExpBoundaryLogEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryAux

theorem homogeneous_classical_fields {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {S : ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hsmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S)) :
    DGClassicalFields (O ×ˢ Ioo 0 S) a (energyDrift a b) (fun _ => 0) u := by
  have hsub : O ×ˢ Ioo (0 : ℝ) S ⊆ O ×ˢ Icc 0 S :=
    Set.prod_mono (Subset.refl _) Ioo_subset_Icc_self
  have hs : SmoothCoefficients (O ×ˢ Ioo 0 S) a b :=
    ⟨hsmooth.1.mono hsub, fun i => (hsmooth.2 i).mono hsub⟩
  exact ⟨fun i j => (matrixEntryCLM i j).contDiff.comp_contDiffOn hs.1,
    energyDrift_smooth (hO.prod isOpen_Ioo) hs, contDiffOn_const, hu⟩

/-- The actual nondivergence equation has the actual derivative-corrected
divergence drift on the physical open slab. -/
theorem homogeneous_classical_divergence {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {S : ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hsmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (heq : ∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = 0) :
    ClassicalDivEq (O ×ˢ Ioo 0 S) a (energyDrift a b) (fun _ => 0) u := by
  intro p hp
  have hus : ContDiffOn ℝ ∞ (fun x => u (x, p.2)) O :=
    hu.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => ⟨hx, hp.2⟩)
  have hus2 : ContDiffAt ℝ 2 (fun x => u (x, p.2)) p.1 :=
    (hus.contDiffAt (hO.mem_nhds hp.1)).of_le (by norm_num)
  have has : ContDiffOn ℝ ∞ (fun x => a (x, p.2)) O :=
    hsmooth.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x hx => ⟨hx, Ioo_subset_Icc_self hp.2⟩)
  have haij (i j : Yau.RIdx n) : DifferentiableAt ℝ (fun x => a (x, p.2) i j) p.1 :=
    (((matrixEntryCLM i j).contDiff.comp_contDiffOn has).contDiffAt
      (hO.mem_nhds hp.1)).differentiableAt (by simp)
  have hflux (i : Yau.RIdx n) :
      d (fun x => ∑ j, a (x, p.2) i j * dgGradient u (x, p.2) j) p.1 i =
        ∑ j, (d (fun x => a (x, p.2) i j) p.1 i * dgGradient u p j +
          a p i j * spatialDD u p (Yau.realVec i) (Yau.realVec j)) := by
    change d (fun x => ∑ j, a (x, p.2) i j * d (fun y => u (y, p.2)) x j) p.1 i = _
    rw [d_sum (f := fun j x => a (x, p.2) i j * d (fun y => u (y, p.2)) x j)
      (fun j => (haij i j).mul (differentiableAt_d hus2 j)) i]
    apply Finset.sum_congr rfl
    intro j _
    rw [d_mul (haij i j) (differentiableAt_d hus2 j), d_d hus2]
    rfl
  have ht : timeD (O ×ˢ Icc 0 S) u p = deriv (fun t => u (p.1, t)) p.2 := by
    have hfiber : {t : ℝ | (p.1, t) ∈ O ×ˢ Icc 0 S} = Icc 0 S := by
      ext t
      simp only [mem_ofPred_eq, mem_prod, hp.1, true_and]
    rw [timeD, hfiber]
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hp.2.1 hp.2.2)
  have hlin := heq p hp
  simp only [linearOp, ht] at hlin
  simp_rw [hflux]
  simp only [energyDrift, Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  have hswap : (∑ i, ∑ j, d (fun x => a (x, p.2) i j) p.1 i * dgGradient u p j) =
      ∑ j, ∑ i, d (fun x => a (x, p.2) i j) p.1 i * dgGradient u p j := Finset.sum_comm
  rw [hswap]
  change deriv (fun t => u (p.1, t)) p.2 - _ = _
  have hgrad (j : Yau.RIdx n) : dgGradient u p j = spatialD u p (Yau.realVec j) := rfl
  simp_rw [hgrad]
  linarith only [hlin]

end Yau.F04Proof
