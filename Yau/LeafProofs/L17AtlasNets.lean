import Yau.LeafProofs.L17ChartEscape

/-! Countable separated nets and the finite-dimensional packing budget. -/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Yau.LeafProofs.L17Aux

theorem exists_countable_separated_net
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    {s : ℝ} (hs : 0 < s) :
    ∃ S : Set X, S.Countable ∧ S.Pairwise (fun x y => s ≤ dist x y) ∧
      ∀ x : X, ∃ p ∈ S, dist x p < s := by
  classical
  obtain ⟨S, hS⟩ := zorn_subset {S : Set X | S.Pairwise (fun x y => s ≤ dist x y)}
    (fun c hc hchain => ⟨⋃₀ c,
      (Set.pairwise_sUnion hchain.directedOn).mpr (fun t ht => hc ht),
      fun t ht => subset_sUnion_of_mem ht⟩)
  have hdisj : S.PairwiseDisjoint (fun p => ball p (s / 3)) := by
    intro p hp q hq hpq
    apply ball_disjoint_ball
    have hd := hS.prop hp hq hpq
    linarith
  have hcount : S.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun p _ => ⟨p, mem_ball_self (by positivity)⟩)
  refine ⟨S, hcount, hS.prop, ?_⟩
  intro x
  by_contra! hnone
  have hins : (insert x S).Pairwise (fun x y => s ≤ dist x y) :=
    hS.prop.insert fun y hy _ => ⟨hnone y hy, by simpa only [dist_comm] using hnone y hy⟩
  have hx := hS.mem_of_prop_insert hins
  have hh := hnone x hx
  simp only [dist_self] at hh
  linarith

theorem exists_intrinsic_countable_net
    {n : ℕ} {M : ComplexManifold n} (g : HermitianField M) (hg : MetricSmooth g)
    {s : ℝ} (hs : 0 < s) :
    ∃ S : Set M.Carrier, S.Countable ∧
      S.Pairwise (fun x y => s ≤ inducedDistance g x y) ∧
      ∀ x : M.Carrier, ∃ p ∈ S, inducedDistance g x p < s := by
  let := L23Aux.metricSpaceOfField g hg
  exact exists_countable_separated_net hs

/-- A finite packing budget, chosen before the separated family or its index type. -/
theorem exists_uniform_packing_bound (n : ℕ) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (ι : Type*) (f : ι → ComplexVector n),
      (∀ i, ‖f i‖ ≤ R) → Pairwise (fun i j => δ ≤ dist (f i) (f j)) →
        Finite ι ∧ Nat.card ι ≤ N := by
  classical
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : ComplexVector n) R).totallyBounded (δ / 3) (by positivity)
  let := ht.to_subtype
  refine ⟨Nat.card t, ?_⟩
  intro ι f hnorm hsep
  have hnear : ∀ i, ∃ q : t, dist (f i) q < δ / 3 := by
    intro i
    have hm : f i ∈ closedBall (0 : ComplexVector n) R := by simpa using hnorm i
    rcases mem_iUnion.mp (hcover hm) with ⟨q, hq⟩
    rcases mem_iUnion.mp hq with ⟨hqt, hqi⟩
    exact ⟨⟨q, hqt⟩, hqi⟩
  choose q hq using hnear
  have hinj : Function.Injective q := by
    intro i j hij
    by_contra hne
    have hi : dist (f i) (q j) < δ / 3 := by simpa only [hij] using hq i
    have hj : dist (q j : ComplexVector n) (f j) < δ / 3 := by
      simpa only [dist_comm] using hq j
    have hd := hsep hne
    have htri := dist_triangle (f i) (q j) (f j)
    linarith
  exact ⟨Finite.of_injective q hinj, Nat.card_le_card_of_injective q hinj⟩

/-- Rescaling removes the chart radius from the packing constant. -/
theorem exists_uniform_scaled_packing_bound (n : ℕ) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ ρ : ℝ, 0 < ρ → ∀ (ι : Type*) (f : ι → ComplexVector n),
      (∀ i, ‖f i‖ ≤ R * ρ) → Pairwise (fun i j => δ * ρ ≤ dist (f i) (f j)) →
        Finite ι ∧ Nat.card ι ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_packing_bound n R δ hδ
  refine ⟨N, ?_⟩
  intro ρ hρ ι f hnorm hsep
  apply hN ι (fun i => (ρ⁻¹ : ℝ) • f i)
  · intro i
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
    calc
      ρ⁻¹ * ‖f i‖ ≤ ρ⁻¹ * (R * ρ) :=
        mul_le_mul_of_nonneg_left (hnorm i) (inv_nonneg.mpr hρ.le)
      _ = R := by field_simp
  · intro i j hij
    rw [dist_smul₀, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
    have h := mul_le_mul_of_nonneg_left (hsep hij) (inv_nonneg.mpr hρ.le)
    convert! h using 1
    field_simp

end Yau.LeafProofs.L17Aux
