import Yau.Proofs.D04L1Bounds
import Yau.Proofs.D04AnchorPropagation

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- A bound on the actual finite-a.e. representative, before passing to an L¹ class. -/
def ActualL1Bound (u : ComplexVector n → EReal) (S : Set (ComplexVector n)) (B : ℝ) : Prop :=
  (∀ᵐ x ∂volume.restrict S, u x ≠ ⊥ ∧ u x ≠ ⊤) ∧
  IntegrableOn (fun x => (u x).toReal) S volume ∧
  (∫ x in S, |(u x).toReal|) ≤ B

/-- Uniform L¹ control on a common tail of a sequence of original potentials. -/
def TailUniformL1 (v : ℕ → ComplexVector n → EReal) (S : Set (ComplexVector n)) : Prop :=
  ∃ (N : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j, N ≤ j → ActualL1Bound (v j) S B

theorem ActualL1Bound.mono {u : ComplexVector n → EReal}
    {S T : Set (ComplexVector n)} {B : ℝ} (h : ActualL1Bound u T B) (hST : S ⊆ T) :
    ActualL1Bound u S B := by
  refine ⟨ae_restrict_of_ae_restrict_of_subset hST h.1, h.2.1.mono_set hST, ?_⟩
  exact (setIntegral_mono_set h.2.1.norm (Eventually.of_forall fun x => abs_nonneg _)
    (Eventually.of_forall hST)).trans h.2.2

theorem ActualL1Bound.union {u : ComplexVector n → EReal}
    {S T : Set (ComplexVector n)} {B C : ℝ}
    (hS : ActualL1Bound u S B) (hT : ActualL1Bound u T C) :
    ActualL1Bound u (S ∪ T) (B + C) := by
  refine ⟨(ae_restrict_union_iff S T _).mpr ⟨hS.1, hT.1⟩, hS.2.1.union hT.2.1, ?_⟩
  have hi := hS.2.1.norm.add_measure hT.2.1.norm
  calc
    (∫ x in S ∪ T, |(u x).toReal|) ≤
        ∫ x, |(u x).toReal| ∂(volume.restrict S + volume.restrict T) :=
      integral_mono_measure (Measure.restrict_union_le _ _)
        (Eventually.of_forall fun x => abs_nonneg _) hi
    _ = (∫ x in S, |(u x).toReal|) + ∫ x in T, |(u x).toReal| :=
      integral_add_measure hS.2.1.norm hT.2.1.norm
    _ ≤ B + C := add_le_add hS.2.2 hT.2.2

theorem TailUniformL1.mono {v : ℕ → ComplexVector n → EReal}
    {S T : Set (ComplexVector n)} (h : TailUniformL1 v T) (hST : S ⊆ T) :
    TailUniformL1 v S := by
  obtain ⟨N, B, hB, h⟩ := h
  exact ⟨N, B, hB, fun j hj => (h j hj).mono hST⟩

theorem TailUniformL1.union {v : ℕ → ComplexVector n → EReal}
    {S T : Set (ComplexVector n)} (hS : TailUniformL1 v S) (hT : TailUniformL1 v T) :
    TailUniformL1 v (S ∪ T) := by
  obtain ⟨N, B, hB, hS⟩ := hS
  obtain ⟨M, C, hC, hT⟩ := hT
  exact ⟨max N M, B + C, add_nonneg hB hC, fun j hj =>
    (hS j ((le_max_left N M).trans hj)).union (hT j ((le_max_right N M).trans hj))⟩

theorem tailUniformL1_finset_biUnion {ι : Type*} {v : ℕ → ComplexVector n → EReal}
    (t : Finset ι) (S : ι → Set (ComplexVector n))
    (hS : ∀ i ∈ t, TailUniformL1 v (S i)) :
    TailUniformL1 v (⋃ i ∈ t, S i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      refine ⟨0, 0, le_rfl, fun j hj => ?_⟩
      simp [ActualL1Bound]
  | insert i t hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hS i (Finset.mem_insert_self _ _)).union
        (ih (fun k hk => hS k (Finset.mem_insert_of_mem hk)))

/-- Compact sets enter the original increasing open domains on a common tail. -/
theorem compact_eventually_subset_open_exhaustion
    {D : Set (ComplexVector n)} {Ωs : ℕ → Set (ComplexVector n)}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = D) {S : Set (ComplexVector n)}
    (hS : IsCompact S) (hSD : S ⊆ D) :
    ∃ N, ∀ j, N ≤ j → S ⊆ Ωs j := by
  have hmono : Monotone Ωs := monotone_nat_of_le_succ (fun j => (hΩ j).2)
  obtain ⟨N, hN⟩ := hS.elim_directed_cover Ωs (fun j => (hΩ j).1)
    (hcover ▸ hSD)
    (fun i j => ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  exact ⟨N, fun j hj => hN.trans (hmono hj)⟩

/-- An open domain contains a triple closed ball about each of its points. -/
theorem exists_triple_closedBall_subset {D : Set (ComplexVector n)}
    (hD : IsOpen D) {x : ComplexVector n} (hx : x ∈ D) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x (3 * ρ) ⊆ D := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD x hx
  refine ⟨ε / 4, by positivity, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith : 3 * (ε / 4) < ε)).trans hball

/-- Tail point anchors may be chosen independently at each index. -/
theorem tailUniformL1_of_point_anchors
    {Ωs : ℕ → Set (ComplexVector n)} {v : ℕ → ComplexVector n → EReal}
    (hv : ∀ j, IsPshOn (v j) (Ωs j))
    {x : ComplexVector n} {ρ q C : ℝ} (hρ : 0 ≤ ρ) (hC : 0 ≤ C) {N : ℕ}
    (hlarge : ∀ j, N ≤ j → Metric.closedBall x (3 * ρ) ⊆ Ωs j)
    (hupper : ∀ j, N ≤ j → ∀ y ∈ Metric.closedBall x (3 * ρ), v j y ≤ (C : EReal))
    (hanchor : ∀ j, N ≤ j → ∃ z ∈ Metric.closedBall x ρ, (q : EReal) ≤ v j z) :
    TailUniformL1 v (Metric.closedBall x ρ) := by
  classical
  choose z hz using (fun k => hanchor (k + N) (Nat.le_add_left N k))
  have hdata := uniform_L1_bound_of_moving_anchor
    (Ωs := fun k => Ωs (k + N)) (us := fun k => v (k + N))
    (fun k => hv (k + N)) hρ
    (fun k => hlarge (k + N) (Nat.le_add_left N k)) hC
    (fun k y hy => hupper (k + N) (Nat.le_add_left N k) y hy) hz
  let B := (2 * C - q) * volume.real (Metric.closedBall (0 : ComplexVector n) (2 * ρ))
  refine ⟨N, max B 0, le_max_right _ _, fun j hj => ?_⟩
  have h := hdata (j - N)
  rw [Nat.sub_add_cancel hj] at h
  exact ⟨h.1, h.2.1, h.2.2.trans (le_max_left _ _)⟩

/-- The open set where original potentials have uniform L¹ control near a point. -/
def L1Good (D : Set (ComplexVector n)) (v : ℕ → ComplexVector n → EReal) :
    Set (ComplexVector n) :=
  {x | ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ D ∧
    TailUniformL1 v (Metric.closedBall x r)}

theorem l1Good_subset {D : Set (ComplexVector n)} {v : ℕ → ComplexVector n → EReal} :
    L1Good D v ⊆ D := by
  rintro x ⟨r, hr, hball, _⟩
  exact hball (Metric.mem_closedBall_self hr.le)

theorem isOpen_l1Good (D : Set (ComplexVector n)) (v : ℕ → ComplexVector n → EReal) :
    IsOpen (L1Good D v) := by
  apply Metric.isOpen_iff.mpr
  rintro x ⟨r, hr, hball, hL1⟩
  refine ⟨r / 2, by positivity, fun y hy => ?_⟩
  have hsub : Metric.closedBall y (r / 2) ⊆ Metric.closedBall x r :=
    Metric.closedBall_subset_closedBall' (by have := Metric.mem_ball.mp hy; linarith)
  exact ⟨r / 2, by positivity, hsub.trans hball, hL1.mono hsub⟩

/-- A fixed compact triple ball has both a common domain and a common upper bound. -/
theorem triple_closedBall_tail_upper
    {D : Set (ComplexVector n)} {Ωs : ℕ → Set (ComplexVector n)}
    {v : ℕ → ComplexVector n → EReal}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = D)
    (hupper : ∀ S ⊆ D, IsCompact S → ∃ C : ℝ, ∀ j, S ⊆ Ωs j →
      ∀ y ∈ S, v j y ≤ (C : EReal))
    {x : ComplexVector n} {ρ : ℝ} (hball : Metric.closedBall x (3 * ρ) ⊆ D) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      (∀ j, N ≤ j → Metric.closedBall x (3 * ρ) ⊆ Ωs j) ∧
      ∀ j, N ≤ j → ∀ y ∈ Metric.closedBall x (3 * ρ), v j y ≤ (C : EReal) := by
  obtain ⟨N, hN⟩ := compact_eventually_subset_open_exhaustion hΩ hcover
    (isCompact_closedBall x (3 * ρ)) hball
  obtain ⟨C, hC⟩ := hupper _ hball (isCompact_closedBall x (3 * ρ))
  refine ⟨N, max C 0, le_max_right _ _, hN, fun j hj y hy => ?_⟩
  exact (hC j (hN j hj) y hy).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))

/-- Uniform L¹ control propagates from any good point in an inner ball to its center. -/
theorem l1Good_of_nearby_good
    {D : Set (ComplexVector n)} {Ωs : ℕ → Set (ComplexVector n)}
    {v : ℕ → ComplexVector n → EReal}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = D) (hv : ∀ j, IsPshOn (v j) (Ωs j))
    (hupper : ∀ S ⊆ D, IsCompact S → ∃ C : ℝ, ∀ j, S ⊆ Ωs j →
      ∀ y ∈ S, v j y ≤ (C : EReal))
    {x y : ComplexVector n} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall x (3 * ρ) ⊆ D)
    (hy : y ∈ Metric.ball x ρ) (hgood : y ∈ L1Good D v) :
    x ∈ L1Good D v := by
  rcases hgood with ⟨r, hr, hrD, Ny, B, hB, hL1⟩
  let δ : ℝ := min r ((ρ - dist y x) / 2)
  have hdist : dist y x < ρ := Metric.mem_ball.mp hy
  have hδ : 0 < δ := lt_min hr (by linarith)
  have hEgood : Metric.closedBall y δ ⊆ Metric.closedBall y r :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hEinner : Metric.closedBall y δ ⊆ Metric.closedBall x ρ :=
    Metric.closedBall_subset_closedBall' (by
      have := min_le_right r ((ρ - dist y x) / 2)
      dsimp [δ]
      linarith)
  obtain ⟨N0, C, hC, hlarge, hCupper⟩ := triple_closedBall_tail_upper hΩ hcover hupper hball
  have hanchors : ∀ j, max N0 Ny ≤ j →
      ∃ z ∈ Metric.closedBall x ρ,
        ((-(B / volume.real (Metric.closedBall y δ)) : ℝ) : EReal) ≤ v j z := by
    intro j hj
    have hdata := (hL1 j ((le_max_right N0 Ny).trans hj)).mono hEgood
    obtain ⟨z, hz, _, _, hzbound⟩ := exists_point_anchor_of_L1_bound volume
      measurableSet_closedBall (Metric.measure_closedBall_pos volume y hδ).ne'
      (isCompact_closedBall y δ).measure_lt_top.ne hdata.1 hdata.2.1 hdata.2.2
    exact ⟨z, hEinner hz, hzbound⟩
  refine ⟨ρ, hρ, (Metric.closedBall_subset_closedBall (by linarith : ρ ≤ 3 * ρ)).trans hball, ?_⟩
  exact tailUniformL1_of_point_anchors hv hρ.le hC
    (fun j hj => hlarge j ((le_max_left N0 Ny).trans hj))
    (fun j hj => hCupper j ((le_max_left N0 Ny).trans hj)) hanchors

/-- On a connected domain, one local L¹ seed controls every compact subset. -/
theorem tailUniformL1_on_compact_of_seed
    {D : Set (ComplexVector n)} (hD : IsOpen D) (hconn : IsConnected D)
    {Ωs : ℕ → Set (ComplexVector n)} {v : ℕ → ComplexVector n → EReal}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = D) (hv : ∀ j, IsPshOn (v j) (Ωs j))
    (hupper : ∀ S ⊆ D, IsCompact S → ∃ C : ℝ, ∀ j, S ⊆ Ωs j →
      ∀ y ∈ S, v j y ≤ (C : EReal))
    (hseed : (L1Good D v).Nonempty) :
    ∀ S ⊆ D, IsCompact S → TailUniformL1 v S := by
  classical
  have hall : D ⊆ L1Good D v := by
    apply hconn.isPreconnected.subset_of_closure_inter_subset (isOpen_l1Good D v)
    · obtain ⟨x, hx⟩ := hseed
      exact ⟨x, l1Good_subset hx, hx⟩
    · rintro x ⟨hxclosure, hxD⟩
      obtain ⟨ρ, hρ, hball⟩ := exists_triple_closedBall_subset hD hxD
      obtain ⟨y, hgood, hy⟩ := Metric.mem_closure_iff.mp hxclosure ρ hρ
      exact l1Good_of_nearby_good hΩ hcover hv hupper hρ hball
        (by simpa [Metric.mem_ball, dist_comm] using hy) hgood
  have hlocal : ∀ x : D, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (x : ComplexVector n) r ⊆ D ∧
      TailUniformL1 v (Metric.closedBall (x : ComplexVector n) r) :=
    fun x => hall x.property
  choose r hr hrD hrL1 using hlocal
  intro S hSD hS
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x : D => Metric.ball x (r x))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hSD hx⟩, Metric.mem_ball_self (hr ⟨x, hSD hx⟩)⟩)
  have hcoverS : S ⊆ ⋃ x ∈ t, Metric.closedBall (x : ComplexVector n) (r x) := by
    intro x hx
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨y, hyt, Metric.ball_subset_closedBall hy⟩
  have hfinite : TailUniformL1 v (⋃ x ∈ t, Metric.closedBall (x : ComplexVector n) (r x)) :=
    tailUniformL1_finset_biUnion (v := v) t
      (fun x : D => Metric.closedBall (x : ComplexVector n) (r x)) (fun x _ => hrL1 x)
  exact TailUniformL1.mono (v := v) hfinite hcoverS

/-- A moving lower anchor in a fixed compact set produces uniform local L¹
control on a strictly increasing extraction, for the original varying domains. -/
theorem uniform_localL1_of_moving_anchor {n : ℕ}
    (D : Set (ComplexVector n)) (hD : IsOpen D) (hconn : IsConnected D)
    (Ωs : ℕ → Set (ComplexVector n)) (us : ℕ → ComplexVector n → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1) ∧ Ωs j ⊆ D)
    (hcover : (⋃ j, Ωs j) = D)
    (hpsh : ∀ j, IsPshOn (us j) (Ωs j))
    (hupper : ∀ K ⊆ D, IsCompact K → ∃ C : ℝ, ∀ j, K ⊆ Ωs j →
      ∀ z ∈ K, us j z ≤ (C : EReal))
    (K : Set (ComplexVector n)) (z : ℕ → ComplexVector n) (A : ℝ)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hanchor : ∀ j, z j ∈ K ∧ z j ∈ Ωs j ∧ ((-A : ℝ) : EReal) ≤ us j (z j)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ S ⊆ D, IsCompact S →
      ∃ (N : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j, N ≤ j →
        S ⊆ Ωs (ψ j) ∧
        (∀ᵐ x ∂volume.restrict S, us (ψ j) x ≠ ⊥ ∧ us (ψ j) x ≠ ⊤) ∧
        IntegrableOn (fun x => (us (ψ j) x).toReal) S volume ∧
        (∫ x in S, |(us (ψ j) x).toReal|) ≤ B := by
  classical
  obtain ⟨x, hxK, ψ, hψ, hconv⟩ := hK.tendsto_subseq (fun j => (hanchor j).1)
  have hmono : Monotone Ωs := monotone_nat_of_le_succ (fun j => (hΩ j).2.1)
  let Ω' : ℕ → Set (ComplexVector n) := fun j => Ωs (ψ j)
  let v : ℕ → ComplexVector n → EReal := fun j => us (ψ j)
  have hΩ' : ∀ j, IsOpen (Ω' j) ∧ Ω' j ⊆ Ω' (j + 1) := fun j =>
    ⟨(hΩ (ψ j)).1, hmono (hψ.monotone (Nat.le_succ j))⟩
  have hcover' : (⋃ j, Ω' j) = D := by
    apply subset_antisymm
    · exact iUnion_subset fun j => (hΩ (ψ j)).2.2
    · intro y hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.symm ▸ hy)
      exact mem_iUnion.mpr ⟨j, hmono (hψ.id_le j) hj⟩
  have hv : ∀ j, IsPshOn (v j) (Ω' j) := fun j => hpsh (ψ j)
  have hupper' : ∀ S ⊆ D, IsCompact S → ∃ C : ℝ, ∀ j, S ⊆ Ω' j →
      ∀ y ∈ S, v j y ≤ (C : EReal) := by
    intro S hSD hS
    obtain ⟨C, hC⟩ := hupper S hSD hS
    exact ⟨C, fun j => hC (ψ j)⟩
  obtain ⟨ρ, hρ, hball⟩ := exists_triple_closedBall_subset hD (hKD hxK)
  obtain ⟨N0, C, hC, hlarge, hCupper⟩ :=
    triple_closedBall_tail_upper hΩ' hcover' hupper' hball
  have hnear : ∀ᶠ j in atTop, (z ∘ ψ) j ∈ Metric.ball x ρ :=
    hconv.eventually (Metric.ball_mem_nhds x hρ)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hnear
  have hseed : (L1Good D v).Nonempty := by
    refine ⟨x, ρ, hρ,
      (Metric.closedBall_subset_closedBall (by linarith : ρ ≤ 3 * ρ)).trans hball, ?_⟩
    apply tailUniformL1_of_point_anchors hv hρ.le hC
      (N := max N0 N1)
      (fun j hj => hlarge j ((le_max_left N0 N1).trans hj))
      (fun j hj => hCupper j ((le_max_left N0 N1).trans hj))
    intro j hj
    exact ⟨z (ψ j), Metric.ball_subset_closedBall (hN1 j ((le_max_right N0 N1).trans hj)),
      (hanchor (ψ j)).2.2⟩
  refine ⟨ψ, hψ, fun S hSD hS => ?_⟩
  obtain ⟨N, B, hB, hdata⟩ :=
    tailUniformL1_on_compact_of_seed hD hconn hΩ' hcover' hv hupper' hseed S hSD hS
  obtain ⟨M, hM⟩ := compact_eventually_subset_open_exhaustion hΩ' hcover' hS hSD
  exact ⟨max N M, B, hB, fun j hj =>
    ⟨hM j ((le_max_right N M).trans hj), hdata j ((le_max_left N M).trans hj)⟩⟩

end Yau.Proofs.D04Aux
