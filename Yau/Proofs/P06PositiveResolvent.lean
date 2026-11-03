import Yau.Proofs.P06Resolvent

noncomputable section
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Filter

section RealHilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem positiveShift_graph_injective (T : H →ₗ.[ℝ] H)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u)) {lam : ℝ} (hlam : 0 < lam)
    {x y x' y' : H} (hxy : (x, y) ∈ T.graph) (hxy' : (x', y') ∈ T.graph)
    (heq : y + lam • x = y' + lam • x') : x = x' := by
  have hdiff := T.graph.sub_mem hxy hxy'
  obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp hdiff
  change (u : H) = x - x' at hu
  change T u = y - y' at hTu
  have hpos : 0 ≤ inner ℝ (x - x') (y - y') := by
    rw [← hu, ← hTu]
    exact hp u
  have hbound := positiveShift_coercive hlam hpos
  have hzero : y - y' + lam • (x - x') = 0 := by
    calc
      _ = (y + lam • x) - (y' + lam • x') := by module
      _ = 0 := sub_eq_zero.mpr heq
  rw [hzero, norm_zero] at hbound
  have hx : ‖x - x'‖ ≤ 0 := (mul_le_mul_iff_left₀ hlam).mp
    (by simpa only [mul_zero, zero_mul, mul_comm] using hbound)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hx (norm_nonneg _)))

variable (T : H →ₗ.[ℝ] H) (hd : Dense (T.domain : Set H)) (hself : T.adjoint = T)
  (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u)) (lam : ℝ) (hlam : 0 < lam)

include hd hself hp hlam

theorem positiveResolvent_exists (f : H) :
    ∃ p : T.graph, (p : H × H).2 + lam • (p : H × H).1 = f := by
  obtain ⟨x, y, hxy, heq⟩ := positiveSelfAdjoint_range T hd hself hp hlam f
  exact ⟨⟨(x, y), hxy⟩, heq⟩

def positiveResolventData (f : H) : T.graph :=
  Classical.choose (positiveResolvent_exists T hd hself hp lam hlam f)

def positiveResolventFun (f : H) : H :=
  (positiveResolventData T hd hself hp lam hlam f : H × H).1

theorem positiveResolventFun_graph (f : H) :
    (positiveResolventFun T hd hself hp lam hlam f,
      f - lam • positiveResolventFun T hd hself hp lam hlam f) ∈ T.graph := by
  let p := positiveResolventData T hd hself hp lam hlam f
  have heq : (p : H × H).2 + lam • (p : H × H).1 = f :=
    Classical.choose_spec (positiveResolvent_exists T hd hself hp lam hlam f)
  have hy : (p : H × H).2 = f - lam • (p : H × H).1 := eq_sub_iff_add_eq.mpr heq
  change ((p : H × H).1, f - lam • (p : H × H).1) ∈ T.graph
  rw [← hy]
  exact p.property

theorem positiveResolventFun_bound (f : H) :
    ‖positiveResolventFun T hd hself hp lam hlam f‖ ≤ lam⁻¹ * ‖f‖ := by
  let x := positiveResolventFun T hd hself hp lam hlam f
  have hg := positiveResolventFun_graph T hd hself hp lam hlam f
  obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp hg
  change (u : H) = x at hu
  change T u = f - lam • x at hTu
  have hpos : 0 ≤ inner ℝ x (f - lam • x) := by rw [← hTu, ← hu]; exact hp u
  have hb := positiveShift_coercive hlam hpos
  rw [sub_add_cancel] at hb
  have hdiv : ‖x‖ ≤ ‖f‖ / lam := (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

def positiveResolventLinear : H →ₗ[ℝ] H where
  toFun := positiveResolventFun T hd hself hp lam hlam
  map_add' f g := by
    apply positiveShift_graph_injective T hp hlam
      (positiveResolventFun_graph T hd hself hp lam hlam (f + g))
      (T.graph.add_mem (positiveResolventFun_graph T hd hself hp lam hlam f)
        (positiveResolventFun_graph T hd hself hp lam hlam g))
    change f + g - lam • positiveResolventFun T hd hself hp lam hlam (f + g) +
      lam • positiveResolventFun T hd hself hp lam hlam (f + g) = _
    module
  map_smul' c f := by
    apply positiveShift_graph_injective T hp hlam
      (positiveResolventFun_graph T hd hself hp lam hlam (c • f))
      (T.graph.smul_mem c (positiveResolventFun_graph T hd hself hp lam hlam f))
    change c • f - lam • positiveResolventFun T hd hself hp lam hlam (c • f) +
      lam • positiveResolventFun T hd hself hp lam hlam (c • f) = _
    module

def positiveResolvent : H →L[ℝ] H :=
  (positiveResolventLinear T hd hself hp lam hlam).mkContinuous lam⁻¹
    (positiveResolventFun_bound T hd hself hp lam hlam)

theorem positiveResolvent_graph (f : H) :
    (positiveResolvent T hd hself hp lam hlam f,
      f - lam • positiveResolvent T hd hself hp lam hlam f) ∈ T.graph :=
  positiveResolventFun_graph T hd hself hp lam hlam f

theorem positiveResolvent_bound (f : H) :
    ‖positiveResolvent T hd hself hp lam hlam f‖ ≤ lam⁻¹ * ‖f‖ :=
  positiveResolventFun_bound T hd hself hp lam hlam f

theorem positiveResolvent_symmetric : (positiveResolvent T hd hself hp lam hlam).IsSymmetric := by
  intro f g
  obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp (positiveResolvent_graph T hd hself hp lam hlam f)
  obtain ⟨v, hv, hTv⟩ := T.mem_graph_iff.mp (positiveResolvent_graph T hd hself hp lam hlam g)
  have hs : T.IsFormalAdjoint T := by simpa only [hself] using T.adjoint_isFormalAdjoint hd
  have h := hs u v
  rw [hu, hv, hTu, hTv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right] at h
  simp only [conj_trivial] at h
  change inner ℝ (positiveResolvent T hd hself hp lam hlam f) g =
    inner ℝ f (positiveResolvent T hd hself hp lam hlam g)
  linarith

theorem positiveResolvent_adjoint : (positiveResolvent T hd hself hp lam hlam).adjoint =
    positiveResolvent T hd hself hp lam hlam :=
  LinearMap.IsSymmetric.clm_adjoint_eq (positiveResolvent_symmetric T hd hself hp lam hlam)

theorem positiveResolvent_inner_nonnegative (f : H) :
    0 ≤ inner ℝ (positiveResolvent T hd hself hp lam hlam f) f := by
  obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp (positiveResolvent_graph T hd hself hp lam hlam f)
  have hn := hp u
  rw [hu, hTu, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hn
  have hm := mul_nonneg hlam.le (sq_nonneg ‖positiveResolvent T hd hself hp lam hlam f‖)
  linarith

theorem positiveResolvent_injective : Function.Injective (positiveResolvent T hd hself hp lam hlam) := by
  intro f g hfg
  obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp (positiveResolvent_graph T hd hself hp lam hlam f)
  obtain ⟨v, hv, hTv⟩ := T.mem_graph_iff.mp (positiveResolvent_graph T hd hself hp lam hlam g)
  have huv : u = v := Subtype.ext (hu.trans (hfg.trans hv.symm))
  have hout := hTu.symm.trans ((congrArg T huv).trans hTv)
  rw [hfg] at hout
  have hout' := congrArg (fun x : H => x + lam • positiveResolvent T hd hself hp lam hlam g) hout
  simpa only [sub_add_cancel] using hout'

theorem positiveResolvent_denseRange : DenseRange (positiveResolvent T hd hself hp lam hlam) := by
  have hk : (positiveResolvent T hd hself hp lam hlam).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (positiveResolvent_injective T hd hself hp lam hlam)
  have heq := (positiveResolvent T hd hself hp lam hlam).orthogonal_ker
  rw [hk, Submodule.bot_orthogonal_eq_top, positiveResolvent_adjoint] at heq
  intro f
  have hf : f ∈ (positiveResolvent T hd hself hp lam hlam).range.topologicalClosure := by
    rw [← heq]
    trivial
  exact hf

end RealHilbert
end Yau.NodeProofs.P06Aux
