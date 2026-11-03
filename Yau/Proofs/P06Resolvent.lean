import Yau.Proofs.P06FormDomain

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux

/-- Coercivity of a positive shift of the graph of a nonnegative operator. -/
theorem positiveShift_coercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x y : H} {lam : ℝ} (hlam : 0 < lam) (hp : 0 ≤ inner ℝ x y) :
    lam * ‖x‖ ≤ ‖y + lam • x‖ := by
  have hi : lam * ‖x‖ ^ 2 ≤ inner ℝ x (y + lam • x) := by
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    linarith
  have hc := real_inner_le_norm x (y + lam • x)
  by_cases hx : ‖x‖ = 0
  · simpa only [hx, mul_zero] using norm_nonneg (y + lam • x)
  · have hxp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    exact (mul_le_mul_iff_right₀ hxp).mp (by nlinarith [hi.trans hc])

/-- A genuine densely defined nonnegative self-adjoint real Hilbert operator
has full positive resolvent range.  Closedness and density are used explicitly. -/
theorem positiveSelfAdjoint_range {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (T : H →ₗ.[ℝ] H)
    (hd : Dense (T.domain : Set H)) (hself : T.adjoint = T)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u))
    {lam : ℝ} (hlam : 0 < lam) (f : H) :
    ∃ x y : H, (x, y) ∈ T.graph ∧ y + lam • x = f := by
  have hclosed : T.IsClosed := by rw [← hself]; exact T.adjoint_isClosed hd
  let C := T.graph
  letI : CompleteSpace C := hclosed.completeSpace_coe
  let F : C →L[ℝ] H :=
    ((ContinuousLinearMap.snd ℝ H H).comp C.subtypeL) +
      lam • ((ContinuousLinearMap.fst ℝ H H).comp C.subtypeL)
  have hF (p : C) : F p = (p : H × H).2 + lam • (p : H × H).1 := rfl
  have hpos (p : C) : 0 ≤ inner ℝ (p : H × H).1 (p : H × H).2 := by
    obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp p.property
    rw [← hu, ← hTu]
    exact hp u
  have hfst (p : C) : ‖(p : H × H).1‖ ≤ lam⁻¹ * ‖F p‖ := by
    have h := positiveShift_coercive hlam (hpos p)
    rw [← hF] at h
    exact (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using h) |>.trans_eq
      (by rw [div_eq_mul_inv, mul_comm])
  have hbound (p : C) : ‖p‖ ≤ max lam⁻¹ 2 * ‖F p‖ := by
    have hsnd : ‖(p : H × H).2‖ ≤ 2 * ‖F p‖ := by
      calc
        ‖(p : H × H).2‖ = ‖F p - lam • (p : H × H).1‖ := by rw [hF]; congr 1; abel
        _ ≤ ‖F p‖ + ‖lam • (p : H × H).1‖ := norm_sub_le _ _
        _ = ‖F p‖ + lam * ‖(p : H × H).1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        _ ≤ ‖F p‖ + lam * (lam⁻¹ * ‖F p‖) := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (hfst p) hlam.le)
        _ = 2 * ‖F p‖ := by rw [← mul_assoc, mul_inv_cancel₀ hlam.ne']; ring
    change max ‖(p : H × H).1‖ ‖(p : H × H).2‖ ≤ _
    apply max_le
    · exact (hfst p).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact hsnd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hrange : IsClosed (F.range : Set H) :=
    (F.antilipschitz_of_bound (K := (⟨max lam⁻¹ 2, by positivity⟩ : NNReal)) hbound).isClosed_range F.uniformContinuous
  have horth : F.rangeᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hpair : ∀ x : T.domain, inner ℝ (-lam • y) (x : H) = inner ℝ y (T x) := by
      intro x
      let p : C := ⟨((x : H), T x), T.mem_graph x⟩
      have hz := ((F.range.mem_orthogonal y).mp hy) (F p) ⟨p, rfl⟩
      rw [hF, inner_add_left, inner_smul_left] at hz
      change inner ℝ (T x) y + lam * inner ℝ (x : H) y = 0 at hz
      calc
        inner ℝ (-lam • y) (x : H) = -lam * inner ℝ (x : H) y := by
          rw [inner_smul_left]
          simp only [conj_trivial]
          congr 1
          exact real_inner_comm _ _
        _ = inner ℝ (T x) y := by linarith
        _ = inner ℝ y (T x) := real_inner_comm _ _
    have hymem : y ∈ T.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists y ⟨-lam • y, hpair⟩
    have hyd : y ∈ T.domain := by simpa only [hself] using hymem
    have he : T ⟨y, hyd⟩ = -lam • y := by
      have ha := LinearPMap.adjoint_apply_eq hd ⟨y, hymem⟩ hpair
      have hgraph : (y, -lam • y) ∈ T.adjoint.graph := by
        rw [← ha]
        exact T.adjoint.mem_graph ⟨y, hymem⟩
      rw [hself] at hgraph
      obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp hgraph
      have hue : u = ⟨y, hyd⟩ := Subtype.ext hu
      rwa [hue] at hTu
    have hn := hp ⟨y, hyd⟩
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at hn
    change 0 ≤ -lam * ‖y‖ ^ 2 at hn
    have hsq : ‖y‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hlam).mp (by nlinarith only [hn])
    have hnorm : ‖y‖ = 0 := by nlinarith only [hsq, norm_nonneg y]
    simpa only [norm_eq_zero.mp hnorm] using (show (0 : H) ∈ (⊥ : Submodule ℝ H) from Submodule.zero_mem _)
  have htop : F.range = ⊤ := by
    rw [← hrange.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.mpr horth
  obtain ⟨p, hp⟩ := (LinearMap.range_eq_top.mp htop : Function.Surjective F) f
  exact ⟨(p : H × H).1, (p : H × H).2, p.property, hp⟩

/-- Nonnegativity passes through genuine graph closure. -/
theorem realClosure_nonnegative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : H →ₗ.[ℝ] H) (hc : T.IsClosable)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u)) :
    ∀ u : T.closure.domain, 0 ≤ inner ℝ (u : H) (T.closure u) := by
  have hclosed : IsClosed {p : H × H | 0 ≤ inner ℝ p.1 p.2} :=
    isClosed_le continuous_const (continuous_fst.inner continuous_snd)
  have hsub : (T.graph : Set (H × H)) ⊆ {p | 0 ≤ inner ℝ p.1 p.2} := by
    intro p hp'
    obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp hp'
    change 0 ≤ inner ℝ p.1 p.2
    rw [← hu, ← hTu]
    exact hp u
  intro u
  have hu : ((u : H), T.closure u) ∈ closure (T.graph : Set (H × H)) := by
    rw [← T.graph.topologicalClosure_coe, hc.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph u
  exact (closure_minimal hsub hclosed) hu

theorem realFormalAdjoint_closure_left {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {D T : H →ₗ.[ℝ] H}
    (hc : D.IsClosable) (hs : D.IsFormalAdjoint T) : D.closure.IsFormalAdjoint T := by
  intro x y
  have hclosed : IsClosed {p : H × H |
      inner ℝ p.2 (y : H) = inner ℝ p.1 (T y)} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hsub : (D.graph : Set (H × H)) ⊆
      {p | inner ℝ p.2 (y : H) = inner ℝ p.1 (T y)} := by
    intro p hp
    obtain ⟨v, hv, hDv⟩ := D.mem_graph_iff.mp hp
    change inner ℝ p.2 (y : H) = inner ℝ p.1 (T y)
    rw [← hv, ← hDv]
    exact hs v y
  have hx : ((x : H), D.closure x) ∈ closure (D.graph : Set (H × H)) := by
    rw [← D.graph.topologicalClosure_coe, hc.graph_closure_eq_closure_graph]
    exact D.closure.mem_graph x
  exact (closure_minimal hsub hclosed) hx

theorem realAdjoint_antitone {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {D C : H →ₗ.[ℝ] H}
    (hd : Dense (D.domain : Set H)) (hC : Dense (C.domain : Set H))
    (hDC : D ≤ C) : C.adjoint ≤ D.adjoint := by
  have hf : C.adjoint.IsFormalAdjoint D := by
    intro x y
    let z : C.domain := ⟨(y : H), hDC.1 y.prop⟩
    have hz : C z = D y := (hDC.2 (show (y : H) = (z : H) from rfl)).symm
    simpa only [hz] using C.adjoint_isFormalAdjoint hC x z
  exact hf.symm.le_adjoint hd

/-- Equality between the closure and adjoint of a symmetric core gives
self-adjointness of that very closure, with no double-adjoint junk branch. -/
theorem realClosure_selfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (T : H →ₗ.[ℝ] H)
    (hd : Dense (T.domain : Set H)) (hc : T.IsClosable)
    (hs : T.IsFormalAdjoint T) (he : T.closure = T.adjoint) :
    T.closure.adjoint = T.closure := by
  have hdc : Dense (T.closure.domain : Set H) := hd.mono T.le_closure.1
  have hsym : T.closure.IsFormalAdjoint T.closure :=
    (realFormalAdjoint_closure_left hc (realFormalAdjoint_closure_left hc hs).symm).symm
  apply le_antisymm
  · have hanti := realAdjoint_antitone hd hdc T.le_closure
    rwa [← he] at hanti
  · exact hsym.le_adjoint hdc

end Yau.NodeProofs.P06Aux
