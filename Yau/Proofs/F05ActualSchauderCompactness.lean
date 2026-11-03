import Yau.Proofs.F05CompatibleJetCompactness
import Yau.Proofs.F05ActualJetGraph
import Yau.Proofs.F05RelativeFullJetHolder

/-! Actual functions with their genuine homogeneous traces have a
subsequence in the original compatible FTC Banach graph at half exponent.
The encoding and all four limiting jets are constructed in the proof. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_actual_schauder_compact_subsequence {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : ℕ → M.Carrier → ℝ → ℝ)
    (hC2 : ∀ k i, C2 (F05Q A i T) (pull A i (w k)))
    (hTuple : ∀ k i, HolderBound α (F05Q A i T)
      (fun z => ((pull A i (w k) z,spatialD (pull A i (w k)) z),
        (spatialDD (pull A i (w k)) z,timeD (F05Q A i T) (pull A i (w k)) z))) C)
    (h0 : ∀ k x, x ∈ closure O → w k x 0 = 0)
    (hTime0 : ∀ k i z, z ∈ F05D A i → timeD (F05Q A i T) (pull A i (w k)) (z,0) = 0)
    (hBoundary : ∀ k x, x ∈ frontier O → ∀ t ∈ Icc 0 T, w k x t = 0) :
    ∃ (φ : ℕ → ℕ) (u : ℕ → F05CompatibleJetGraph A (α/2) hT)
      (uLim : F05CompatibleJetGraph A (α/2) hT),
      StrictMono φ ∧ Tendsto (fun k => u (φ k)) atTop (𝓝 uLim) ∧
      ∀ k i (p : F05Q A i T),
        ((u k).val i).val.1 p = pull A i (w k) p.val ∧
        ((u k).val i).val.2.1 p = spatialD (pull A i (w k)) p.val ∧
        ((u k).val i).val.2.2.1.val.1 p = spatialDD (pull A i (w k)) p.val ∧
        ((u k).val i).val.2.2.2.val.1 p = timeD (F05Q A i T) (pull A i (w k)) p.val := by
  have hHalf : 0 < α/2 := by positivity
  have hSch (k : ℕ) (i : Fin A.count) :
      SchauderBound (α/2) (F05Q A i T) (pull A i (w k)) (2*C) :=
    F05_schauder_lower_exponent hHalf.le (by linarith)
      (F05_schauder_of_full_jet_holder (hC2 k i) (hTuple k i))
  let u : ℕ → F05CompatibleJetGraph A (α/2) hT := fun k =>
    F05ActualJetGraph hA hHalf hT (w k) (hSch k) (h0 k) (hTime0 k) (hBoundary k)
  have hEval (k : ℕ) (i : Fin A.count) (p : F05Q A i T) :=
    F05ActualJetAmbient_eval hA hHalf hT (w k) (hSch k) (h0 k) (hTime0 k) (hBoundary k) i p
  have hEncoded (k : ℕ) (i : Fin A.count) :
      HolderBound α (F05Q A i T) (F05JetComponentTuple ((u k).val i).val) C := by
    apply holderBound_congr_on (hTuple k i)
    intro p hp
    change ((pull A i (w k) p,spatialD (pull A i (w k)) p),
      (spatialDD (pull A i (w k)) p,timeD (F05Q A i T) (pull A i (w k)) p)) =
      ((F05BCFFun ((u k).val i).val.1 p,F05BCFFun ((u k).val i).val.2.1 p),
        (vectorHolderFun ((u k).val i).val.2.2.1 p,holderGraphFun ((u k).val i).val.2.2.2 p))
    rw [F05BCFFun_apply _ ⟨p,hp⟩,F05BCFFun_apply _ ⟨p,hp⟩,
      vectorHolderFun_apply _ ⟨p,hp⟩,holderGraphFun_apply _ ⟨p,hp⟩]
    exact (Prod.ext (Prod.ext (hEval k i ⟨p,hp⟩).1 (hEval k i ⟨p,hp⟩).2.1)
      (Prod.ext (hEval k i ⟨p,hp⟩).2.2.1 (hEval k i ⟨p,hp⟩).2.2.2)).symm
  obtain ⟨φ,uLim,hφ,hLim⟩ := F05_compatible_jet_compact_subsequence A hα hT u hEncoded
  exact ⟨φ,u,uLim,hφ,hLim,hEval⟩

end Yau.Proofs.F05Aux
