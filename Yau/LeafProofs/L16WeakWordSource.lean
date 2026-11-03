import Yau.LeafProofs.L16WeakSourceCalculus

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Classical spatial word derivatives, used only on smooth coefficients and tests. -/
def coefficientSpatialWord {n : ℕ} : List (Yau.RIdx n) → (Point n → ℝ) → Point n → ℝ
  | [], g => g
  | i::w, g => fun p => fderiv ℝ (coefficientSpatialWord w g) p (Yau.realVec i,0)

theorem coefficientSpatialWord_regular {n : ℕ} {g : Point n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (w : List (Yau.RIdx n)) :
    ContDiff ℝ ∞ (coefficientSpatialWord w g) ∧ HasCompactSupport (coefficientSpatialWord w g) := by
  induction w with
  | nil => exact ⟨hg,hcg⟩
  | cons i w ih =>
    exact ⟨(ih.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
      ih.2.fderiv_apply ℝ (Yau.realVec i,0)⟩

/-- Finite sums over lists preserve multiplicities in the weak derivative identity. -/
theorem weakGradientOn_list_sum {n : ℕ} {Q : Set (Point n)}
    {ι : Type*} (xs : List ι) (u : ι → Point n → ℝ)
    (G : ι → Point n → Yau.RIdx n → ℝ)
    (hu : ∀ k ∈ xs, MemLp (u k) 2 (volume.restrict Q))
    (hG : ∀ k ∈ xs, ∀ i, MemLp (fun p => G k p i) 2 (volume.restrict Q))
    (hWeak : ∀ k ∈ xs, WeakGradientOn Q (u k) (G k)) :
    MemLp (fun p => (xs.map (fun k => u k p)).sum) 2 (volume.restrict Q) ∧
      (∀ i, MemLp (fun p => (xs.map (fun k => G k p i)).sum) 2 (volume.restrict Q)) ∧
      WeakGradientOn Q (fun p => (xs.map (fun k => u k p)).sum)
        (fun p i => (xs.map (fun k => G k p i)).sum) := by
  induction xs with
  | nil =>
    simpa only [List.map_nil,List.sum_nil] using
      (And.intro (MemLp.zero' : MemLp (fun _ : Point n => (0 : ℝ)) 2 (volume.restrict Q))
      (And.intro (fun _ : Yau.RIdx n => (MemLp.zero' : MemLp (fun _ : Point n => (0 : ℝ)) 2 (volume.restrict Q)))
        (weakGradientOn_zero Q)))
  | cons k xs ih =>
    have hs := ih (fun z hz => hu z (List.mem_cons_of_mem _ hz))
      (fun z hz => hG z (List.mem_cons_of_mem _ hz))
      (fun z hz => hWeak z (List.mem_cons_of_mem _ hz))
    have huSum : MemLp (fun p => u k p+(xs.map (fun z => u z p)).sum) 2 (volume.restrict Q) := by
      convert! (hu k List.mem_cons_self).add hs.1 using 1
    have hGSum (i : Yau.RIdx n) :
        MemLp (fun p => G k p i+(xs.map (fun z => G z p i)).sum) 2 (volume.restrict Q) := by
      convert! (hG k List.mem_cons_self i).add (hs.2.1 i) using 1
    simpa only [List.map_cons,List.sum_cons] using
      (And.intro huSum (And.intro hGSum
        (weakGradientOn_add (hu k List.mem_cons_self) hs.1
          (hG k List.mem_cons_self) hs.2.1 (hWeak k List.mem_cons_self) hs.2.2)))

def weakWordCorrection {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (s t : List (Yau.RIdx n)) (p : Point n) : ℝ :=
  ∑ j, coefficientSpatialWord s (g j) p*U (j::t) p

def weakWordSource {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) : ℝ :=
  ((commutatorSplits w).map (fun st => weakWordCorrection g U st.1 st.2 p)).sum

def weakWordSourceGradient {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) (i : Yau.RIdx n) : ℝ :=
  ((commutatorSplits w).map (fun st =>
    weakWordCorrection g U (i::st.1) st.2 p+weakWordCorrection g U st.1 (i::st.2) p)).sum

theorem weakWordSource_cons {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (i : Yau.RIdx n) (p : Point n) :
    weakWordSource g U (i::w) p =
      weakWordCorrection g U [i] w p+weakWordSourceGradient g U w p i := by
  simp only [weakWordSource,weakWordSourceGradient,commutatorSplits,List.map_cons,List.sum_cons,
    List.map_flatMap,List.map_nil]
  rw [list_sum_flatMap_pairs]

theorem weakWordSource_nil {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) : weakWordSource g U [] = 0 := by
  funext p
  simp only [weakWordSource,commutatorSplits,List.map_nil,List.sum_nil,Pi.zero_apply]

theorem weakWordSource_weakH1 {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (g : Yau.RIdx n → Point n → ℝ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hcg : ∀ j, HasCompactSupport (g j))
    (U : List (Yau.RIdx n) → Point n → ℝ) (k : ℕ)
    (hL2 : ∀ v, v.length ≤ k+1 → MemLp (U v) 2 (volume.restrict Q))
    (hWG : ∀ v, v.length ≤ k → WeakGradientOn Q (U v) (fun p i => U (i::v) p))
    (w : List (Yau.RIdx n)) (hw : w.length ≤ k) :
    MemLp (weakWordSource g U w) 2 (volume.restrict Q) ∧
      (∀ i, MemLp (fun p => weakWordSourceGradient g U w p i) 2 (volume.restrict Q)) ∧
      WeakGradientOn Q (weakWordSource g U w) (weakWordSourceGradient g U w) := by
  have hEach (st : List (Yau.RIdx n) × List (Yau.RIdx n)) (hst : st ∈ commutatorSplits w) :
      MemLp (weakWordCorrection g U st.1 st.2) 2 (volume.restrict Q) ∧
        (∀ i, MemLp (fun p => weakWordCorrection g U (i::st.1) st.2 p+
          weakWordCorrection g U st.1 (i::st.2) p) 2 (volume.restrict Q)) ∧
        WeakGradientOn Q (weakWordCorrection g U st.1 st.2)
          (fun p i => weakWordCorrection g U (i::st.1) st.2 p+
            weakWordCorrection g U st.1 (i::st.2) p) := by
    have hLen := commutatorSplits_lower_length w st hst
    have hTail : st.2.length ≤ k := by omega
    have hOne (j : Yau.RIdx n) : (j::st.2).length ≤ k := by simp only [List.length_cons]; omega
    have hTwo (i j : Yau.RIdx n) : (i::j::st.2).length ≤ k+1 := by simp only [List.length_cons]; omega
    have hSwap : ∀ᵐ p ∂volume.restrict Q, ∀ i j, U (i::j::st.2) p = U (j::i::st.2) p :=
      weak_second_spatial_derivatives_commute_ae hQ (hWG st.2 hTail)
        (fun i j => hL2 (i::j::st.2) (hTwo i j)) (fun j => hWG (j::st.2) (hOne j))
    have hRaw := weakGradientOn_weighted_finset_sum Finset.univ
      (fun j => coefficientSpatialWord st.1 (g j)) (fun j => U (j::st.2))
      (fun j p i => U (i::j::st.2) p)
      (fun j _ => hL2 (j::st.2) (by simp only [List.length_cons]; omega))
      (fun j _ i => hL2 (i::j::st.2) (hTwo i j))
      (fun j _ => hWG (j::st.2) (hOne j))
      (fun j _ => (coefficientSpatialWord_regular (hg j) (hcg j) st.1).1)
      (fun j _ => (coefficientSpatialWord_regular (hg j) (hcg j) st.1).2)
    have hGradEq (i : Yau.RIdx n) :
        (fun p => ∑ j, (coefficientSpatialWord st.1 (g j) p*U (i::j::st.2) p+
          U (j::st.2) p*fderiv ℝ (coefficientSpatialWord st.1 (g j)) p (Yau.realVec i,0))) =ᵐ[volume.restrict Q]
        (fun p => weakWordCorrection g U (i::st.1) st.2 p+weakWordCorrection g U st.1 (i::st.2) p) := by
      filter_upwards [hSwap] with p hp
      dsimp only [weakWordCorrection,coefficientSpatialWord]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hp i j]
      ring
    exact ⟨hRaw.1,fun i => (memLp_congr_ae (hGradEq i)).mp (hRaw.2.1 i),
      weakGradientOn_congr_ae hRaw.2.2 (Filter.Eventually.of_forall (fun _ => rfl)) hGradEq⟩
  exact weakGradientOn_list_sum (commutatorSplits w)
    (fun st => weakWordCorrection g U st.1 st.2)
    (fun st p i => weakWordCorrection g U (i::st.1) st.2 p+weakWordCorrection g U st.1 (i::st.2) p)
    (fun st hst => (hEach st hst).1) (fun st hst => (hEach st hst).2.1)
    (fun st hst => (hEach st hst).2.2)

end Yau.LeafProofs.L16Aux
