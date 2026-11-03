import Yau.Proofs.F05PatchContinuity
import Yau.Proofs.F05CanonicalRegularity

/-! The concrete canonical realization is jointly continuous on the full
closed time slab, including both the initial and lateral faces. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05CanonicalJetFunction_continuousOn {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le) :
    ContinuousOn (fun p : M.Carrier × ℝ => F05CanonicalJetFunction A χ α hT.le u p.1 p.2)
      (univ ×ˢ Icc 0 T) := by
  have hTerm (j : Fin A.count) : ContinuousOn
      (fun p : M.Carrier × ℝ => χ j p.1*F05LocalJetExtension A j (F05InnerPlateau n)
        (u.val j).val (F05Coord A j p.1,p.2)) (univ ×ˢ Icc 0 T) := by
    let uj : F05LocalFTCGraph A j α hT.le := ⟨(u.val j).val,(u.val j).property.1.1.1⟩
    have hExtension := F05_local_extension_jets A j α hT uj (F05InnerPlateau n)
      F05InnerPlateau_contDiff F05InnerPlateau_tsupport
    exact F05ManifoldPatch_continuousOn hA j (hχ.1 j)
      ((hχ.2.2.1 j).trans (image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 3/4))))
      hExtension.1.1
  unfold F05CanonicalJetFunction
  exact continuousOn_finset_sum Finset.univ (fun j _ => hTerm j)

end Yau.Proofs.F05Aux
