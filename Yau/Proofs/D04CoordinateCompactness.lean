import Yau.Proofs.D04CoordinateGlue
import Yau.Proofs.D04Diagonal

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- The exact local conclusions carried by one actual extraction stage. -/
def CoordinateStageData (O : Set (ComplexVector n)) (us : ℕ → ComplexVector n → EReal)
    (s : ℕ → ℕ) (v : ComplexVector n → EReal) : Prop :=
  IsPshOn v O ∧ CoordinateLocallyL1Converges O (fun j => us (s j)) v ∧
    (∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O →
      Tendsto (fun j => ∫⁻ y in K, erealDist (us (s j) y) (v y)) atTop (𝓝 0)) ∧
    (∀ c : ℝ, (∀ y ∈ O, v y = (c : EReal)) →
      ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop, ∀ y ∈ K, us (s j) y ≤ ((c + ε : ℝ) : EReal))

/-- Varying domains require one separate tail on each relatively compact
open set. Nested extraction and exact tail factorization produce a single
original subsequence and the frozen coordinate L¹ alternative. -/
theorem pshL1Limit_of_eventual_localL1
    {D : Set (ComplexVector n)} (hD : IsOpen D) (hne : D.Nonempty)
    (Ωs : ℕ → Set (ComplexVector n)) (us : ℕ → ComplexVector n → EReal)
    (hpsh : ∀ j, IsPshOn (us j) (Ωs j))
    (hL1 : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ D →
      ∃ (N : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j, N ≤ j →
        K ⊆ Ωs j ∧ (∀ᵐ y ∂volume.restrict K, us j y ≠ ⊥ ∧ us j y ≠ ⊤) ∧
          IntegrableOn (fun y => (us j y).toReal) K volume ∧
          (∫ y in K, |(us j y).toReal|) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ PshL1Limit D us φ := by
  classical
  obtain ⟨O, K, hOK, hOmono, hcover⟩ := exists_nested_open_compact_exhaustion hD
  choose N B hB htail using fun m => hL1 (K m) (hOK m).2.1 (hOK m).2.2.2.2
  have hstage (m : ℕ) (s : ℕ → ℕ) (hs : StrictMono s) :
      ∃ r : ℕ → ℕ, StrictMono r ∧
        ∃ v : ComplexVector n → EReal, CoordinateStageData (O m) us (s ∘ r) v := by
    have hj (j : ℕ) : N m ≤ s (j + N m) :=
      (show N m ≤ j + N m by omega).trans (hs.id_le _)
    have hu : ∀ j, IsPshOn (us (s (j + N m))) (O m) ∧
        CoordinateLocallyL1 (O m) (us (s (j + N m))) := by
      intro j
      have hdata := htail m (s (j + N m)) (hj j)
      refine ⟨isPshOn_mono (hpsh _) ((hOK m).2.2.1.trans hdata.1), ?_⟩
      intro S hS hSO
      have hSK := hSO.trans (hOK m).2.2.1
      exact ⟨ae_restrict_of_ae_restrict_of_subset hSK hdata.2.1, hdata.2.2.1.mono_set hSK⟩
    have hbound : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O m →
        ∃ C : ℝ, ∀ j, ∫ y in S, |(us (s (j + N m)) y).toReal| ≤ C := by
      intro S hS hSO
      refine ⟨B m, ?_⟩
      intro j
      have hdata := htail m (s (j + N m)) (hj j)
      exact (setIntegral_mono_set hdata.2.2.1.norm
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (Filter.Eventually.of_forall (hSO.trans (hOK m).2.2.1))).trans hdata.2.2.2
    obtain ⟨τ, v, hτ, hv, hvc, hvd, hvh⟩ := coordinate_psh_L1_compactness (hOK m).1 hu hbound
    refine ⟨fun j => τ j + N m, ?_, v, hv, hvc, hvd, hvh⟩
    exact fun i j hij => Nat.add_lt_add_right (hτ hij) _
  let S := {s : ℕ → ℕ // StrictMono s}
  let pickR (m : ℕ) (s : S) : ℕ → ℕ := Classical.choose (hstage m s.1 s.2)
  have pickRStrict (m : ℕ) (s : S) : StrictMono (pickR m s) :=
    (Classical.choose_spec (hstage m s.1 s.2)).1
  let pickV (m : ℕ) (s : S) : ComplexVector n → EReal :=
    Classical.choose (Classical.choose_spec (hstage m s.1 s.2)).2
  have pickData (m : ℕ) (s : S) :
      CoordinateStageData (O m) us (s.1 ∘ pickR m s) (pickV m s) :=
    Classical.choose_spec (Classical.choose_spec (hstage m s.1 s.2)).2
  let next (m : ℕ) (s : S) : S := ⟨s.1 ∘ pickR m s, s.2.comp (pickRStrict m s)⟩
  let states : ℕ → S := Nat.rec ⟨id, strictMono_id⟩ next
  let ss : ℕ → ℕ → ℕ := fun m => (states m).1
  let rr : ℕ → ℕ → ℕ := fun m => pickR m (states m)
  let vv : ℕ → ComplexVector n → EReal := fun m => pickV m (states m)
  have hs (m : ℕ) : StrictMono (ss m) := (states m).2
  have hr (m : ℕ) : StrictMono (rr m) := pickRStrict m (states m)
  have hrec (m k : ℕ) : ss (m + 1) k = ss m (rr m k) := rfl
  have hdata (m : ℕ) : CoordinateStageData (O m) us (ss (m + 1)) (vv m) := pickData m (states m)
  obtain ⟨φ, hφ, hfactor⟩ := nested_subsequence_diagonal ss rr hs hr hrec
  refine ⟨φ, hφ, ?_⟩
  have hinput : ∀ T : Set (ComplexVector n), IsCompact T → T ⊆ D →
      ∃ M : ℕ, ∀ j, M ≤ j → IntegrableOn (fun y => (us (φ j) y).toReal) T volume := by
    intro T hT hTD
    obtain ⟨M, C, hC, hTdata⟩ := hL1 T hT hTD
    exact ⟨M, fun j hj => (hTdata (φ j) (hj.trans (hφ.id_le j))).2.2.1⟩
  have hreal : ∀ m T, IsCompact T → T ⊆ O m →
      Tendsto (fun j => ∫ y in T, |(us (φ j) y).toReal - (vv m y).toReal|) atTop (𝓝 0) := by
    intro m T hT hTO
    obtain ⟨τ, hτ, heq⟩ := hfactor m
    exact tendsto_of_subsequence_tail
      (fun j => ∫ y in T, |(us j y).toReal - (vv m y).toReal|) hτ heq
      ((hdata m).2.1.2 T hT hTO)
  have hdist : ∀ m T, IsCompact T → T ⊆ O m →
      Tendsto (fun j => ∫⁻ y in T, erealDist (us (φ j) y) (vv m y)) atTop (𝓝 0) := by
    intro m T hT hTO
    obtain ⟨τ, hτ, heq⟩ := hfactor m
    exact tendsto_of_subsequence_tail
      (fun j => ∫⁻ y in T, erealDist (us j y) (vv m y)) hτ heq
      ((hdata m).2.2.1 T hT hTO)
  have hhartogs : ∀ (m : ℕ) (c : ℝ), (∀ y ∈ O m, vv m y = (c : EReal)) →
      ∀ T, IsCompact T → T ⊆ O m → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop, ∀ y ∈ T, us (φ j) y ≤ ((c + ε : ℝ) : EReal) := by
    intro m c hc T hT hTO ε hε
    obtain ⟨τ, hτ, heq⟩ := hfactor m
    exact eventually_of_subsequence_tail
      (P := fun j => ∀ y ∈ T, us j y ≤ ((c + ε : ℝ) : EReal))
      hτ heq ((hdata m).2.2.2 c hc T hT hTO ε hε)
  have hglue := pshL1Limit_of_nested_local_limits hD hne O
    (fun m => ⟨(hOK m).1, (hOK m).2.2.1.trans (hOK m).2.2.2.2⟩)
    hOmono hcover (fun j => us (φ j)) vv (fun m => (hdata m).1)
    (fun m => (hdata m).2.1.1) hinput hreal hdist hhartogs
  simpa only [PshL1Limit, id_eq] using hglue

end Yau.Proofs.D04Aux
