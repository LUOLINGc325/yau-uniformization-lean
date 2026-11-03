import Yau.LeafProofs.L16ExpBoundaryLocalModulus

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Explicit controls on the actual operator, derivatives and zero data. This
transparent conjunction is used only to abbreviate the finite-cover theorem. -/
def ZeroDataControl {n : ℕ} (O : Set (Space n)) (T ν upper A₀ b₀ H W₀ : ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ) : Prop :=
  Elliptic (O ×ˢ Ioo 0 T) a ν upper ∧
    (∀ z ∈ O ×ˢ Ioo 0 T, ∀ i j, |a z i j| ≤ A₀) ∧
    (∀ z ∈ O ×ˢ Ioo 0 T, ∀ i, |b z i| ≤ b₀) ∧
    ContinuousOn u (cylinder (closure O) 0 T) ∧
    (∀ z ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun y => u (y,z.2)) z.1) ∧
    (∀ z ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2) ∧
    (∀ z ∈ closure O, u (z,0) = 0) ∧
    (∀ z ∈ frontier O, ∀ t ∈ Icc 0 T, u (z,t) = 0) ∧
    (∀ z ∈ cylinder (closure O) 0 T, |u z| ≤ W₀) ∧
    ∀ z ∈ O ×ˢ Ioo 0 T, |linearOp (cylinder (closure O) 0 T) a b u z| ≤ H

/-- Compactness selects the boundary constant before the coefficient fields
and solution. Both nearby and distant pairs are covered. -/
theorem smoothDomain_uniform_boundary_pair_modulus {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {T ν upper A₀ b₀ H W₀ : ℝ}
    (hT : 0 < T) (hν : 0 < ν) (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀)
    (hH : 0 < H) (hW₀ : 0 < W₀) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ),
        ZeroDataControl O T ν upper A₀ b₀ H W₀ a b u →
        ∀ y ∈ frontier O, ∀ z ∈ closure O, ∀ t ∈ Icc 0 T,
          |u (z,t)| ≤ K*‖z-y‖ := by
  classical
  have hCharts (x : frontier O) : ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ),
        ZeroDataControl O T ν upper A₀ b₀ H W₀ a b u →
        ∀ y ∈ frontier O ∩ Metric.ball x.val r,
          ∀ z ∈ closure O ∩ Metric.ball y r, ∀ t ∈ Icc 0 T, |u (z,t)| ≤ K*‖z-y‖ := by
    obtain ⟨s,R,a₀,M₁,M₂,S₀,hR,ha₀,hM₁,hM₂,hS₀,hs,hjets,hnonneg,hzero⟩ :=
      smoothDomain_local_defining_data hO x.property
    obtain ⟨K,hK,hlocal⟩ := local_boundary_modulus_of_defining_data hO.1 hO.2.2.1
      hT hν hA₀ hb₀ hH hW₀ hR ha₀ hM₁ hM₂ hs hjets hnonneg hzero
    refine ⟨R/4,K,by positivity,hK,?_⟩
    intro a b u hdata
    rcases hdata with ⟨he,hA,hb,hc,hs,ht,hi,hl,hsup,hop⟩
    exact hlocal a b u he hA hb hc hs ht hi hl hsup hop
  choose r K hr hK hlocal using hCharts
  have hcompact : IsCompact (frontier O) :=
    hO.2.2.1.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨s,hs⟩ := hcompact.elim_finite_subcover
    (fun x : frontier O => Metric.ball x.val (r x)) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩)
  obtain ⟨r₀,hr₀,hr₀le⟩ := L16Aux.finite_pos_lower_bound s r (fun x _ => hr x)
  let C : ℝ := 1+(∑ x ∈ s, K x)+W₀/r₀
  have hsum : 0 ≤ ∑ x ∈ s, K x := Finset.sum_nonneg (fun x _ => (hK x).le)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro a b u hdata y hy z hz t ht
  by_cases hnear : ‖z-y‖ < r₀
  · obtain ⟨i,his,hyi⟩ := mem_iUnion₂.mp (hs hy)
    have hzr : z ∈ Metric.ball y (r i) := by
      change dist z y < r i
      rw [dist_eq_norm]
      exact hnear.trans_le (hr₀le i his)
    have hEst := hlocal i a b u hdata y ⟨hy,hyi⟩ z ⟨hz,hzr⟩ t ht
    have hKi : K i ≤ ∑ x ∈ s, K x :=
      Finset.single_le_sum (fun x _ => (hK x).le) his
    have hKC : K i ≤ C := by dsimp [C]; nlinarith [div_nonneg hW₀.le hr₀.le]
    exact hEst.trans (mul_le_mul_of_nonneg_right hKC (norm_nonneg _))
  · have hfar : r₀ ≤ ‖z-y‖ := le_of_not_gt hnear
    have hsup : |u (z,t)| ≤ W₀ := by
      rcases hdata with ⟨_,_,_,_,_,_,_,_,hvalue,_⟩
      exact hvalue (z,t) ⟨hz,ht⟩
    have hratio : W₀ ≤ (W₀/r₀)*‖z-y‖ := by
      have hm := mul_le_mul_of_nonneg_left hfar (div_nonneg hW₀.le hr₀.le)
      simpa only [div_mul_cancel₀ W₀ hr₀.ne'] using hm
    have hle : W₀/r₀ ≤ C := by dsimp [C]; linarith
    exact hsup.trans (hratio.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _)))

theorem smoothDomain_frontier_nonempty {n : ℕ} (hn : 0 < n) {O : Set (Space n)}
    (hO : SmoothDomain O) : (frontier O).Nonempty := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  haveI : Nontrivial (Space n) := inferInstance
  have hne : O ≠ univ := by
    intro heq
    exact hO.2.2.1.ne_univ (by simp [heq])
  obtain ⟨x,hx⟩ := hO.2.1
  obtain ⟨y,hy,hDist⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hne
  exact ⟨y,hy⟩

/-- A genuine nearest boundary point converts the uniform pair estimate to
the actual metric distance from the boundary. -/
theorem smoothDomain_uniform_boundary_distance_modulus {n : ℕ} (hn : 0 < n)
    {O : Set (Space n)} (hO : SmoothDomain O) {T ν upper A₀ b₀ H W₀ : ℝ}
    (hT : 0 < T) (hν : 0 < ν) (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀)
    (hH : 0 < H) (hW₀ : 0 < W₀) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ),
        ZeroDataControl O T ν upper A₀ b₀ H W₀ a b u →
        ∀ z ∈ cylinder (closure O) 0 T,
          |u z| ≤ K*Metric.infDist z.1 (frontier O) := by
  obtain ⟨K,hK,hEst⟩ := smoothDomain_uniform_boundary_pair_modulus hO hT hν hA₀ hb₀ hH hW₀
  refine ⟨K,hK,?_⟩
  intro a b u hdata z hz
  obtain ⟨y,hy,heq⟩ := isClosed_frontier.exists_infDist_eq_dist (smoothDomain_frontier_nonempty hn hO) z.1
  have h := hEst a b u hdata y hy z.1 hz.1 z.2 hz.2
  simpa only [heq,dist_eq_norm] using h

end Yau.LeafProofs.L16ExpBoundaryAux
