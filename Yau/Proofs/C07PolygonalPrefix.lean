import Yau.Proofs.C07PolygonalPrefixPartition
import Yau.Proofs.C07PolygonalPrefixConcat
import Yau.Proofs.C07PolygonalPrefixSegment

open scoped Manifold Topology unitInterval

noncomputable section

namespace Yau.Proofs.C07PolygonalPrefixAux

open Yau Set C07Aux D04AtlasGlueAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Locally in the row parameter, every prefix of a continuous based square
has an integrable polygonal replacement, jointly continuous in both parameters,
with one compact image set and one length bound. -/
theorem exists_local_polygonal_prefix (hg : MetricSmooth g) (o : M.Carrier)
    (H : C(I × I, M.Carrier)) (h0 : ∀ s : I, H (0, s) = o) (s₀ : I) :
    ∃ N : Set I, IsOpen N ∧ s₀ ∈ N ∧
      ∃ (K : Set M.Carrier) (L : ℝ), IsCompact K ∧ 0 ≤ L ∧
        ∃ (γ : ∀ a : I × N, IntegrableCurve g o (H (a.1, a.2.1)))
          (P : C(I × (I × N), M.Carrier)),
          (∀ u a, P (u, a) = (γ a).1 u) ∧
          (∀ a, curveLength g (γ a).1 ≤ L) ∧
          (∀ a u, u ∈ Icc (0 : ℝ) 1 → (γ a).1 u ∈ K) ∧
          (∀ s : N, ∀ u ∈ Icc (0 : ℝ) 1, (γ (0, s)).1 u = o) := by
  classical
  obtain ⟨balls, hballs⟩ := exists_countable_chartBalls M
  obtain ⟨m, t, b, N, hm, ht0, htm, htmono, hN, hsN, hpiece⟩ :=
    exists_local_partition H (fun i => (balls i).inner)
      (fun i => (balls i).isOpen_inner) hballs s₀
  let B : Fin m → ChartBall M := fun i => balls (b i)
  let K : Set M.Carrier := ⋃ i : Fin m,
    chartBallMap (B i) '' Metric.closedBall 0 (2 * (B i).radius)
  have hK : IsCompact K := isCompact_iUnion (fun i => chartBallMap_compact_outer (B i))
  have hBK : ∀ i : Fin m,
      chartBallMap (B i) '' Metric.closedBall 0 (2 * (B i).radius) ⊆ K :=
    fun i => subset_iUnion (fun j : Fin m =>
      chartBallMap (B j) '' Metric.closedBall 0 (2 * (B j).radius)) i
  have hHK : ∀ u : I, ∀ s : N, H (u, s.1) ∈ K := by
    intro u s
    obtain ⟨i, hi⟩ := exists_partition_piece hm t ht0 htm u
    have hu : H (u, s.1) ∈ (B i).outer :=
      (B i).core_subset_outer ((B i).inner_subset_core (hpiece i s.1 s.2 u hi))
    exact hBK i ⟨chartBallCoord (B i) (H (u, s.1)),
      Metric.ball_subset_closedBall (chartBallCoord_outer (B i) hu),
      chartBallMap_coord (B i) hu⟩
  have hsegments : ∀ i : Fin m, ∃ L : ℝ, 0 ≤ L ∧
      ∃ (γ : ∀ a : I × N,
          IntegrableCurve g (H (min a.1 (t i), a.2.1)) (H (min a.1 (t (i + 1)), a.2.1)))
        (P : C(I × (I × N), M.Carrier)),
        (∀ u a, P (u, a) = (γ a).1 u) ∧
        (∀ a, curveLength g (γ a).1 ≤ L) ∧
        (∀ a u, u ∈ Icc (0 : ℝ) 1 → (γ a).1 u ∈ K) ∧
        (∀ s : N, ∀ u ∈ Icc (0 : ℝ) 1, (γ (0, s)).1 u = o) := by
    intro i
    exact exists_segment_family hg H N (B i) (t i) (t (i + 1))
      (htmono (Nat.le_succ i)) (fun s u hu => hpiece i s.1 s.2 u hu)
      K hHK (hBK i) o h0
  choose L hL γ P hP hlen himg hbase using hsegments
  let v : ℕ → C(I × N, M.Carrier) := fun i =>
    ⟨fun a => H (min a.1 (t i), a.2.1), H.continuous.comp
      ((continuous_fst.min continuous_const).prodMk (continuous_subtype_val.comp continuous_snd))⟩
  let ℓ : ℕ → ℝ := fun i => if hi : i < m then L ⟨i, hi⟩ else 0
  have hv0 : ∀ a : I × N, v 0 a = o := by
    intro a
    dsimp only [v, ContinuousMap.coe_mk]
    rw [ht0, min_eq_right (show (0 : I) ≤ a.1 from a.1.2.1)]
    exact h0 a.2.1
  have hvlast : ∀ a : I × N, v m a = H (a.1, a.2.1) := by
    intro a
    dsimp only [v, ContinuousMap.coe_mk]
    rw [htm, min_eq_left (show a.1 ≤ (1 : I) from a.1.2.2)]
  obtain ⟨ζ, Q, hQ, hζL, hζK, hζB⟩ :=
    finite_concat m v ℓ K {a : I × N | a.1 = 0} o
      (fun a => hHK _ a.2) (fun a _ => hv0 a) (by
        intro i hi
        refine ⟨γ ⟨i, hi⟩, P ⟨i, hi⟩, hP ⟨i, hi⟩, ?_, himg ⟨i, hi⟩, ?_⟩
        · simpa only [ℓ, dif_pos hi] using hlen ⟨i, hi⟩
        · intro a ha u hu
          rcases a with ⟨a, s⟩
          change a = 0 at ha
          subst a
          exact hbase ⟨i, hi⟩ s u hu)
  let Γ : ∀ a : I × N, IntegrableCurve g o (H (a.1, a.2.1)) :=
    fun a => repointCurve (ζ a) (hv0 a) (hvlast a)
  refine ⟨N, hN, hsN, K, ∑ i ∈ Finset.range m, ℓ i, hK, ?_, Γ, Q, ?_, ?_, ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro i hi
    dsimp only [ℓ]
    split_ifs with h
    · exact hL ⟨i, h⟩
    · exact le_rfl
  · exact hQ
  · exact hζL
  · exact hζK
  · intro s u hu
    exact hζB (0, s) rfl u hu

end Yau.Proofs.C07PolygonalPrefixAux
