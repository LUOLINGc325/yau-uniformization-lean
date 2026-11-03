import Yau.Proofs.F01SpatialWordsTensorJets
import Yau.Proofs.F01CompactSmoothHolder
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-! Taylor composition through any fixed order is an actual smooth map
of the finite jets. This is the native Faa di Bruno polynomial, with its
ordered partitions and all operator tensor norms retained. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

abbrev FiniteTaylorJet (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :=
  (j : Fin (k + 1)) → ContinuousMultilinearMap ℝ (fun _ : Fin j.val => E) F

def finiteTaylorComposition (k : ℕ)
    (w : FiniteTaylorJet F G k × FiniteTaylorJet E F k) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G :=
  ∑ c : OrderedFinpartition k,
    c.compAlongOrderedFinpartition (w.1 ⟨c.length, Nat.lt_succ_of_le c.length_le⟩)
      (fun i => w.2 ⟨c.partSize i, Nat.lt_succ_of_le (c.partSize_le i)⟩)

theorem finiteTaylorComposition_smooth (k : ℕ) :
    ContDiff ℝ ∞ (finiteTaylorComposition (E := E) (F := F) (G := G) k) := by
  unfold finiteTaylorComposition
  apply ContDiff.sum
  intro c _
  let B := c.compAlongOrderedFinpartitionL ℝ E F G
  have hB : ContDiff ℝ ∞ (fun w :
      (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => F) G) ×
      ((i : Fin c.length) → ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => E) F) =>
      B w.1 w.2) :=
    B.analyticOnNhd_uncurry_of_multilinear.contDiff
  have hInputs : ContDiff ℝ ∞ (fun x : FiniteTaylorJet F G k × FiniteTaylorJet E F k =>
      (x.1 ⟨c.length, Nat.lt_succ_of_le c.length_le⟩,
        fun i => x.2 ⟨c.partSize i, Nat.lt_succ_of_le (c.partSize_le i)⟩)) := by
    apply ContDiff.prodMk
    · exact (contDiff_apply ℝ
        (fun j : Fin (k + 1) => ContinuousMultilinearMap ℝ (fun _ : Fin j.val => F) G)
        ⟨c.length, Nat.lt_succ_of_le c.length_le⟩).comp contDiff_fst
    · apply contDiff_pi.mpr
      intro i
      exact (contDiff_apply ℝ
        (fun j : Fin (k + 1) => ContinuousMultilinearMap ℝ (fun _ : Fin j.val => E) F)
        ⟨c.partSize i, Nat.lt_succ_of_le (c.partSize_le i)⟩).comp contDiff_snd
  exact hB.comp hInputs

theorem finiteTaylorComposition_eq_taylorComp (k : ℕ)
    (q : FormalMultilinearSeries ℝ F G) (p : FormalMultilinearSeries ℝ E F) :
    finiteTaylorComposition k ((fun j => q j.val), (fun j => p j.val)) = q.taylorComp p k := rfl

theorem finiteTaylorComposition_native {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (k : ℕ) :
    finiteTaylorComposition k
      ((fun j => iteratedFDeriv ℝ j.val g (f x)), (fun j => iteratedFDeriv ℝ j.val f x)) =
      iteratedFDeriv ℝ k (g ∘ f) x := by
  exact (finiteTaylorComposition_eq_taylorComp k (ftaylorSeries ℝ g (f x))
    (ftaylorSeries ℝ f x)).trans
      (iteratedFDeriv_comp hg hf (by simp : (k : ℕ∞ω) ≤ ∞)).symm

theorem continuousMultilinearMap_finiteDimensional
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) := by
  let J : (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin k => E) F :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective

end Yau.NodeProofs.F01Aux
