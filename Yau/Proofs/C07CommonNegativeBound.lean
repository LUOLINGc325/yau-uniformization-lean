import Yau.Proofs.C07NegativeSubsequence
import Yau.Proofs.C07CofinalSequence

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

/-- The negative bound holds for the full physical-time family. A violating
compact would select bad clocks along which the genuine psh compactness and
Liouville alternatives both force a stronger negative bound. -/
theorem common_negative_bound {n : ℕ} (X : KahlerManifold n)
    (g : HermitianField X.manifold) (hg : MetricSmooth g)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume g μ) (hLiouville : PshLiouville X)
    (Ω : ℝ → Set (Pt X)) (v : ℝ → Pt X → EReal) (T₀ : ℝ)
    (hopen : ∀ t, T₀ ≤ t → IsOpen (Ω t)) (hmono : MonotoneOn Ω (Ici T₀))
    (hexhaust : ∀ K : Set (Pt X), IsCompact K → ∃ T, ∀ t, T ≤ t → K ⊆ Ω t)
    (hpsh : ∀ t, T₀ ≤ t → PshOnManifold (v t) (Ω t))
    (hupper : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ t,
      T₀ ≤ t → K ⊆ Ω t → ∀ x ∈ K, v t x ≤ (C : EReal))
    (hzero : ∀ K : Set (Pt X), IsCompact K → ∃ T, ∀ t, T ≤ t →
      ∀ x ∈ K, v t x ≤ (0 : EReal))
    (K₀ : Set (Pt X)) (hK₀ : IsCompact K₀) (hμK₀ : 0 < μ K₀)
    {a : ℝ} (ha : 0 < a)
    (hnegative : ∃ T, ∀ t, T ≤ t → ∀ x ∈ K₀, v t x ≤ ((-a : ℝ) : EReal)) :
    ∀ K : Set (Pt X), IsCompact K → ∃ T, ∀ t, T ≤ t →
      ∀ x ∈ K, v t x ≤ ((-a / 4 : ℝ) : EReal) := by
  intro K hK
  by_contra hbad
  push_neg at hbad
  obtain ⟨tk, htk, htkInf, hall⟩ := cofinal_strictMono_sequence hbad T₀
  let Ωs := fun j => Ω (tk j)
  let us := fun j => v (tk j)
  have hΩs : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1) := by
    intro j
    exact ⟨hopen _ (hall j).1,
      hmono (hall j).1 (hall (j + 1)).1 (htk.monotone (Nat.le_succ j))⟩
  have hcover : (⋃ j, Ωs j) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨T, hT⟩ := hexhaust {x} isCompact_singleton
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htkInf.eventually (eventually_ge_atTop T))
    exact mem_iUnion.mpr ⟨N, hT (tk N) (hN N le_rfl) (mem_singleton x)⟩
  have hpshs : ∀ j, PshOnManifold (us j) (Ωs j) := fun j => hpsh _ (hall j).1
  have huppers : ∀ J : Set (Pt X), IsCompact J → ∃ C : ℝ, ∀ j,
      J ⊆ Ωs j → ∀ x ∈ J, us j x ≤ (C : EReal) := by
    intro J hJ
    obtain ⟨C, hC⟩ := hupper J hJ
    exact ⟨C, fun j => hC _ (hall j).1⟩
  have hzeros : ∀ J : Set (Pt X), IsCompact J → ∃ N, ∀ j, N ≤ j →
      ∀ x ∈ J, us j x ≤ (0 : EReal) := by
    intro J hJ
    obtain ⟨T, hT⟩ := hzero J hJ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htkInf.eventually (eventually_ge_atTop T))
    exact ⟨N, fun j hj => hT _ (hN j hj)⟩
  have hnegs : ∃ N, ∀ j, N ≤ j → ∀ x ∈ K₀, us j x ≤ ((-a : ℝ) : EReal) := by
    obtain ⟨T, hT⟩ := hnegative
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htkInf.eventually (eventually_ge_atTop T))
    exact ⟨N, fun j hj => hT _ (hN j hj)⟩
  obtain ⟨φ, hφ, hneg⟩ := negative_psh_subsequence X g hg μ hμ hLiouville Ωs us
    hΩs hcover hpshs huppers hzeros K₀ hK₀ hμK₀ ha hnegs
  obtain ⟨N, hN⟩ := hneg K hK
  obtain ⟨x, hx, hbadx⟩ := (hall (φ N)).2.2
  have hb := hN N le_rfl x hx
  have hcompare : ((-a / 2 : ℝ) : EReal) ≤ ((-a / 4 : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (by linarith)
  exact (not_lt_of_ge (hb.trans hcompare)) hbadx

end Yau.Proofs.C07Aux
