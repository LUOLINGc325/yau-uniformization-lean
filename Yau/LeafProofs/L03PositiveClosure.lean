import Mathlib

noncomputable section

namespace Yau.LeafProofs.L03

open LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Positivity makes the sum of the two coordinates of an operator graph coercive. -/
private theorem norm_fst_le_norm_add {x y : H} (hp : 0 ≤ inner ℝ x y) :
    ‖x‖ ≤ ‖x + y‖ := by
  have hi : ‖x‖ ^ 2 ≤ inner ℝ x (x + y) := by
    rw [inner_add_right, real_inner_self_eq_norm_sq]
    linarith
  have hc := real_inner_le_norm x (x + y)
  nlinarith [norm_nonneg x, norm_nonneg (x + y)]

/-- A densely defined symmetric nonnegative real Hilbert space operator is
essentially self-adjoint if its adjoint has no eigenvector with eigenvalue `-1`. -/
theorem positive_closure_eq_adjoint
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →ₗ.[ℝ] H)
    (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u))
    (hk : ∀ u : T.adjoint.domain, T.adjoint u = -(u : H) → (u : H) = 0) :
    T.closure = T.adjoint := by
  have hta : T ≤ T.adjoint := hs.le_adjoint hd
  have hcl : T.IsClosable := (LinearPMap.adjoint_isClosed hd).isClosable.leIsClosable hta
  have hca : T.closure ≤ T.adjoint := by
    apply LinearPMap.le_of_le_graph
    rw [← hcl.graph_closure_eq_closure_graph]
    exact T.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hta)
      (LinearPMap.adjoint_isClosed hd)
  let C := T.graph.topologicalClosure
  have hcclosed : IsClosed (C : Set (H × H)) := T.graph.isClosed_topologicalClosure
  let : CompleteSpace C := hcclosed.completeSpace_coe
  have hpos : ∀ p : C, 0 ≤ inner ℝ (p : H × H).1 (p : H × H).2 := by
    have hz : IsClosed {p : H × H | 0 ≤ inner ℝ p.1 p.2} :=
      isClosed_le continuous_const (continuous_fst.inner continuous_snd)
    intro p
    apply hz.closure_subset_iff.mpr ?_ p.property
    intro q hq
    obtain ⟨u, rfl⟩ := (T.mem_graph_iff').mp hq
    exact hp u
  let A : C →L[ℝ] H :=
    ((ContinuousLinearMap.fst ℝ H H).comp C.subtypeL) +
      ((ContinuousLinearMap.snd ℝ H H).comp C.subtypeL)
  have ha (p : C) : A p = (p : H × H).1 + (p : H × H).2 := rfl
  have hbound : ∀ p : C, ‖p‖ ≤ (2 : ℝ) * ‖A p‖ := by
    intro p
    have hf := norm_fst_le_norm_add (hpos p)
    have hsnd : ‖(p : H × H).2‖ ≤ 2 * ‖A p‖ := by
      calc
        ‖(p : H × H).2‖ = ‖A p - (p : H × H).1‖ := by rw [ha]; congr 1; abel
        _ ≤ ‖A p‖ + ‖(p : H × H).1‖ := norm_sub_le _ _
        _ ≤ 2 * ‖A p‖ := by rw [← ha] at hf; linarith
    change max ‖(p : H × H).1‖ ‖(p : H × H).2‖ ≤ _
    rw [max_le_iff]
    constructor
    · rw [← ha] at hf
      exact hf.trans (by nlinarith [norm_nonneg (A p)])
    · exact hsnd
  have harange : IsClosed (A.range : Set H) :=
    (A.antilipschitz_of_bound (K := 2) hbound).isClosed_range A.uniformContinuous
  have haorth : A.rangeᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have heq : ∀ x : T.domain, inner ℝ (-y) (x : H) = inner ℝ y (T x) := by
      intro x
      let p : C := ⟨((x : H), T x), T.graph.le_topologicalClosure (T.mem_graph x)⟩
      have hz := ((A.range.mem_orthogonal y).mp hy) (A p) (by exact ⟨p, rfl⟩)
      rw [ha, inner_add_left] at hz
      change inner ℝ (x : H) y + inner ℝ (T x) y = 0 at hz
      rw [inner_neg_left, real_inner_comm (x : H) y, real_inner_comm (T x) y]
      linarith
    have hydom : y ∈ T.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists y ⟨-y, heq⟩
    have hyzero : y = 0 := hk ⟨y, hydom⟩ (LinearPMap.adjoint_apply_eq hd _ heq)
    simpa using hyzero
  have hatop : A.range = ⊤ := by
    rw [← harange.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.mpr haorth
  have hasurj : Function.Surjective A := LinearMap.range_eq_top.mp hatop
  apply le_antisymm hca
  apply LinearPMap.le_of_le_graph
  intro z hz
  obtain ⟨u, rfl⟩ := (T.adjoint.mem_graph_iff').mp hz
  obtain ⟨p, hpu⟩ := hasurj ((u : H) + T.adjoint u)
  have hpgraph : (p : H × H) ∈ T.closure.graph := by
    rw [← hcl.graph_closure_eq_closure_graph]
    exact p.property
  obtain ⟨v, hv⟩ := (T.closure.mem_graph_iff').mp hpgraph
  let v' : T.adjoint.domain := ⟨v, hca.1 v.property⟩
  have hva : T.adjoint v' = T.closure v := (hca.2 (show (v : H) = v' from rfl)).symm
  have hsum : (v : H) + T.closure v = (u : H) + T.adjoint u := by
    rw [ha, ← hv] at hpu
    exact hpu
  have hw : T.adjoint (u - v') = -((u - v' : T.adjoint.domain) : H) := by
    rw [LinearPMap.map_sub, hva]
    change T.adjoint u - T.closure v = -((u : H) - (v : H))
    calc
      T.adjoint u - T.closure v = (v : H) - (u : H) := by
        apply sub_eq_sub_iff_add_eq_add.mpr
        simpa only [add_comm] using hsum.symm
      _ = -((u : H) - (v : H)) := by abel
  have huv : (u : H) = (v : H) := sub_eq_zero.mp (hk (u - v') hw)
  have hTv : T.adjoint u = T.closure v := by
    have huveq : u = v' := Subtype.ext huv
    rw [huveq, hva]
  rw [huv, hTv]
  exact T.closure.mem_graph v

end Yau.LeafProofs.L03
