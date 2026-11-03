import Yau.Proofs.F05ActualSourceLinear
import Yau.LeafProofs.L16ResidualEstimates

/-! Actual nonlinear scalar functions with proved Holder bounds on a ball
encode in the original initial-zero source graph, retaining the norm bound. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_actual_source_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {α T r K F₀ : ℝ} (hα : 0 < α) (hT : 0 ≤ T) (hr : 0 < r) (hK : 0 ≤ K) (hF₀ : 0 ≤ F₀)
    (F : E → M.Carrier → ℝ → ℝ)
    (hDiff : ∀ u v : E, ‖u‖ ≤ r → ‖v‖ ≤ r → ∀ i : Fin A.count,
      HolderBound α (F05Q A i T) (fun p => pull A i (F u) p-pull A i (F v) p) (K*‖u-v‖))
    (hInit : ∀ u : E, ‖u‖ ≤ r → ∀ x ∈ closure O, F u x 0 = 0)
    (hZero : ∀ i, HolderBound α (F05Q A i T) (pull A i (F 0)) F₀) :
    ∃ N : E → F05SourceZeroGraph A α T,
      (∀ u : E, ‖u‖ ≤ r → ∀ i (p : F05Q A i T), holderGraphFun ((N u).val i) p.val = pull A i (F u) p.val) ∧
      ‖N 0‖ ≤ F₀ ∧ ∀ u v : E, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ K*‖u-v‖ := by
  classical
  have hZeroBall : ‖(0 : E)‖ ≤ r := by simpa only [norm_zero] using hr.le
  have hHolder (u : E) (hu : ‖u‖ ≤ r) (i : Fin A.count) :
      HolderBound α (F05Q A i T) (pull A i (F u)) (K*‖u‖+F₀) := by
    have hh := holderBound_add (hDiff u 0 hu hZeroBall i) (hZero i)
    simp only [sub_zero] at hh
    apply holderBound_congr_on hh
    intro p hp
    ring
  let encode := fun u (hu : ‖u‖ ≤ r) => F05ActualSourceZero hA hα hT (F u) (hHolder u hu) (hInit u hu)
  let N := fun u => if hu : ‖u‖ ≤ r then encode u hu else 0
  have hValue (u : E) (hu : ‖u‖ ≤ r) (i : Fin A.count) (p : F05Q A i T) :
      holderGraphFun ((N u).val i) p.val = pull A i (F u) p.val := by
    rw [show N u = encode u hu from dite_eq_left hu]
    exact F05ActualSourceZero_eval hA hα hT (F u) (hHolder u hu) (hInit u hu) i p
  refine ⟨N,hValue,?_,?_⟩
  · apply (pi_norm_le_iff_of_nonneg hF₀).mpr
    intro i
    apply holderGraph_norm_le_of_holderBound ((N 0).val i)
    exact holderBound_congr_on (hZero i) (fun p hp => (hValue 0 hZeroBall i ⟨p,hp⟩).symm)
  · intro u v hu hv
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg _))).mpr
    intro i
    apply holderGraph_norm_le_of_holderBound (((N u-N v).val) i)
    apply holderBound_congr_on (hDiff u v hu hv i)
    intro p hp
    change pull A i (F u) p-pull A i (F v) p = holderGraphFun ((N u).val i-(N v).val i) p
    have hSub : holderGraphFun ((N u).val i-(N v).val i) p =
        holderGraphFun ((N u).val i) p-holderGraphFun ((N v).val i) p := by
      rw [holderGraphFun_apply _ ⟨p,hp⟩,holderGraphFun_apply _ ⟨p,hp⟩,holderGraphFun_apply _ ⟨p,hp⟩]
      rfl
    rw [hSub,hValue u hu i ⟨p,hp⟩,hValue v hv i ⟨p,hp⟩]

end Yau.Proofs.F05Aux
