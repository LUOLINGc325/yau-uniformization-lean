import Yau.Proofs.F01CommutatorWordPairs
import Yau.Proofs.F01SpatialWordsTensorJets

/-! Actual native-frame words are evaluations of the full spatial jet
on unit vectors. Their Holder constants are therefore unchanged, and
the finite commutator words retain the same native-frame property. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def NativeFrameWord (vs : List (Space n)) : Prop :=
  ∀ v ∈ vs, ∃ i : RIdx n, v = realVec i

theorem realVec_norm_one (i : RIdx n) : ‖realVec i‖ = 1 := by
  by_cases hi : i.2 = 0 <;>
    simp [realVec, hi, norm_smul, EuclideanSpace.single, PiLp.norm_single]

theorem nativeFrameWord_ofFn {vs : List (Space n)} (hv : NativeFrameWord vs) :
    ∃ m : Fin vs.length → RIdx n, vs = List.ofFn (fun j => realVec (m j)) := by
  have he : ∀ j : Fin vs.length, ∃ i : RIdx n, vs.get j = realVec i :=
    fun j => hv _ (List.get_mem vs j)
  choose m hm using he
  exact ⟨m, (List.ofFn_get vs).symm.trans (congrArg List.ofFn (funext hm))⟩

theorem nativeFrameWord_commutator_pairs (vs : List (Space n)) (hv : NativeFrameWord vs) :
    ∀ ab ∈ linearSpatialCommutatorPairs vs, NativeFrameWord ab.1 ∧ NativeFrameWord ab.2 := by
  induction vs with
  | nil => simp [linearSpatialCommutatorPairs]
  | cons v vs ih =>
    have hvv := hv v (by simp)
    have hvs : NativeFrameWord vs := fun w hw => hv w (by simp [hw])
    intro ab hab
    rcases List.mem_cons.mp hab with h | h
    · subst ab
      constructor
      · intro w hw
        have he : w = v := by simpa using hw
        obtain ⟨i, hi⟩ := hvv
        exact ⟨i, he.trans hi⟩
      · exact hvs
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        obtain ⟨ha, hb⟩ := ih hvs p hp
        refine ⟨?_, hb⟩
        intro w hw
        rcases List.mem_cons.mp hw with he | he
        · obtain ⟨i, hi⟩ := hvv
          exact ⟨i, he.trans hi⟩
        · exact ha w he
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        obtain ⟨ha, hb⟩ := ih hvs p hp
        refine ⟨ha, ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with he | he
        · obtain ⟨i, hi⟩ := hvv
          exact ⟨i, he.trans hi⟩
        · exact hb w he

theorem native_frame_word_holder_of_tensor {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Q : Set (Point n)} {S : Set (Space n)} {β C : ℝ} {f : Point n → G}
    (hS : IsOpen S) (hQ : Q ⊆ S ×ˢ (Set.univ : Set ℝ))
    (hf : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S)
    (vs : List (Space n)) (hv : NativeFrameWord vs)
    (hJet : HolderBound β Q
      (fun p => iteratedFDeriv ℝ vs.length (fun z => f (z, p.2)) p.1) C) :
    HolderBound β Q (spatialDerivativeWord vs f) C := by
  obtain ⟨m, hm⟩ := nativeFrameWord_ofFn hv
  have hUnit : ‖(fun j : Fin vs.length => realVec (m j))‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact (realVec_norm_one _).le
  have he : ∀ p ∈ Q, spatialDerivativeWord vs f p =
      iteratedFDeriv ℝ vs.length (fun z => f (z, p.2)) p.1 (fun j => realVec (m j)) := by
    intro p hp
    exact (congrArg (fun w => spatialDerivativeWord w f p) hm).trans
      (spatialDerivativeWord_ofFn_eq_iteratedFDeriv hS (hf p hp) vs.length _ (hQ hp).1)
  refine ⟨hJet.1, ?_, ?_⟩
  · intro p hp
    change ‖spatialDerivativeWord vs f p‖ ≤ C
    rw [he p hp]
    exact (ContinuousMultilinearMap.unit_le_opNorm _ hUnit).trans (hJet.2.1 p hp)
  · intro p hp q hq
    change ‖spatialDerivativeWord vs f p - spatialDerivativeWord vs f q‖ ≤ _
    rw [he p hp, he q hq]
    have hh := ContinuousMultilinearMap.unit_le_opNorm
      (iteratedFDeriv ℝ vs.length (fun z => f (z, p.2)) p.1 -
        iteratedFDeriv ℝ vs.length (fun z => f (z, q.2)) q.1) hUnit
    apply le_trans ?_ (hJet.2.2 p hp q hq)
    simpa only [sub_apply] using hh

end Yau.NodeProofs.F01Aux
