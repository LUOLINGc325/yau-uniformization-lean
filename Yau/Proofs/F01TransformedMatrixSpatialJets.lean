import Yau.Proofs.F01SliceLeviTensorHolder
import Yau.Proofs.F01FiniteTaylorHolder

/-! The same genuine differentiated-potential Hessians control all jets
of background plus native Levi. A common constant is selected before
both fields, the chart domain and Holder exponent. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

local instance transformedMatrixJetLeviOpNorm (n : ℕ) :
    Norm ((Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  ContinuousLinearMap.hasOpNorm

theorem transformed_matrix_spatial_jet_holder_budget (k : ℕ) {Cs Cu : ℝ}
    (hCs : 0 ≤ Cs) (hCu : 0 ≤ Cu) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β : ℝ)
      (A : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ),
      IsOpen S → Q ⊆ S ×ˢ (Set.univ : Set ℝ) →
      HolderBound β Q A Cs →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => A (z, p.2)) S) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) S) →
      (∀ j : Fin (k + 1),
        HolderBound β Q (fun p => iteratedFDeriv ℝ j.val (fun z => A (z, p.2)) p.1) Cs) →
      (∀ j : Fin (k + 1), ∀ m : Fin j.val → RIdx n,
        HolderBound β Q (spatialDD
          (spatialDerivativeWord (List.ofFn (fun i => realVec (m i))) u)) Cu) →
      HolderBound β Q (fun p => A p + leviC (fun z => u (z, p.2)) p.1) C ∧
      ∀ j : Fin (k + 1), HolderBound β Q
        (fun p => iteratedFDeriv ℝ j.val
          (fun z => A (z, p.2) + leviC (fun w => u (w, p.2)) z) p.1) C := by
  have hEach : ∀ j : Fin (k + 1), ∃ Cj : ℝ, 0 < Cj ∧
      ∀ (Q : Set (Point n)) (S : Set (Space n)) (β B : ℝ) (u : Point n → ℝ),
      IsOpen S → 0 ≤ B → Q ⊆ S ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) S) →
      (∀ m : Fin j.val → RIdx n, HolderBound β Q (spatialDD
        (spatialDerivativeWord (List.ofFn (fun i => realVec (m i))) u)) B) →
      HolderBound β Q (fun p => iteratedFDeriv ℝ j.val
        (fun z => leviC (fun w => u (w, p.2)) z) p.1) (Cj * B) :=
    fun j => levi_tensor_holder_budget_of_slices j.val
  choose Cj hCj hj using hEach
  let N : ℝ := ‖leviSecondMatrixCLM (n := n)‖
  have hN : 0 ≤ N := ContinuousLinearMap.opNorm_nonneg _
  let C : ℝ := 1 + Cs + N * Cu + ∑ j, Cj j * Cu
  have hSum : 0 ≤ ∑ j, Cj j * Cu :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hCj j).le hCu)
  have hC : 0 < C := by dsimp only [C]; linarith [mul_nonneg hN hCu]
  have hBudget (j : Fin (k + 1)) : Cs + Cj j * Cu ≤ C := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => mul_nonneg (hCj i).le hCu) (Finset.mem_univ j)
    dsimp only [C]
    linarith [mul_nonneg hN hCu]
  refine ⟨C, hC, ?_⟩
  intro Q S β A u hS hQ hA hs hu hAj hDD
  have hSmoothLevi : ∀ p ∈ Q,
      ContDiffOn ℝ ∞ (fun z => leviC (fun w => u (w, p.2)) z) S :=
    fun p hp => native_levi_frobenius_contDiffOn hS (hu p hp)
  have hLevi := native_levi_holder_of_spatialDD (fun p hp =>
    ((hu p hp).contDiffAt
      (hS.mem_nhds (hQ hp).1)).of_le (by simp))
    (by simpa only [List.ofFn_zero, spatialDerivativeWord] using
      hDD (⟨0, by omega⟩ : Fin (k + 1)) (fun i => Fin.elim0 i))
  refine ⟨holderBound_mono_const (holderBound_add hA hLevi) ?_, ?_⟩
  · dsimp only [C]
    linarith
  · intro j
    have hL := hj j Q S β Cu u hS hCu hQ hu (hDD j)
    have hAdd := holderBound_add (hAj j) hL
    have he : ∀ p ∈ Q,
        iteratedFDeriv ℝ j.val
          (fun z => A (z, p.2) + leviC (fun w => u (w, p.2)) z) p.1 =
        iteratedFDeriv ℝ j.val (fun z => A (z, p.2)) p.1 +
          iteratedFDeriv ℝ j.val (fun z => leviC (fun w => u (w, p.2)) z) p.1 := by
      intro p hp
      exact fun_iteratedFDeriv_add_apply
        (((hs p hp).contDiffAt (hS.mem_nhds (hQ hp).1)).of_le (by simp))
        (((hSmoothLevi p hp).contDiffAt (hS.mem_nhds (hQ hp).1)).of_le (by simp))
    have hb : HolderBound β Q
        (fun p => iteratedFDeriv ℝ j.val
          (fun z => A (z, p.2) + leviC (fun w => u (w, p.2)) z) p.1) (Cs + Cj j * Cu) := by
      refine ⟨hAdd.1, ?_, ?_⟩
      · intro p hp
        change ‖iteratedFDeriv ℝ j.val
          (fun z => A (z, p.2) + leviC (fun w => u (w, p.2)) z) p.1‖ ≤ _
        rw [he p hp]
        exact hAdd.2.1 p hp
      · intro p hp q hq
        change ‖iteratedFDeriv ℝ j.val
          (fun z => A (z, p.2) + leviC (fun w => u (w, p.2)) z) p.1 -
          iteratedFDeriv ℝ j.val
          (fun z => A (z, q.2) + leviC (fun w => u (w, q.2)) z) q.1‖ ≤ _
        rw [he p hp, he q hq]
        exact hAdd.2.2 p hp q hq
    exact holderBound_mono_const hb (hBudget j)

end Yau.NodeProofs.F01Aux
