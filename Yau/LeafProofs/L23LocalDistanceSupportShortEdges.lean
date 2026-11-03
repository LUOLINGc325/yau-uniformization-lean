import Yau.LeafProofs.L23LocalDistanceSupportPolygonExact
import Yau.LeafProofs.L23FieldMetricLocalNormal

/-! Exact compact polygons have uniformly short edges in local pair neighborhoods. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem uniform_pairs_of_compact {α : Type*} [MetricSpace α]
    (S : Set α) (hS : IsCompact S) (P : α → α → Prop)
    (hP : ∀ x ∈ S, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ z ∈ U, P y z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ y : α, dist x y < δ → P x y := by
  choose U hU hmem hpairs using (fun x : S => hP x.val x.property)
  have hcover : S ⊆ ⋃ x : S, U x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hleb⟩ := lebesgue_number_lemma_of_metric hS hU hcover
  refine ⟨δ,hδ,?_⟩
  intro x hx y hxy
  obtain ⟨i,hi⟩ := hleb x hx
  apply hpairs i x (hi (Metric.mem_ball_self hδ)) y
  exact hi (by simpa only [Metric.mem_ball,dist_comm] using hxy)

theorem exists_fieldPolygon_exact_with_short_edges
    (h : HermitianField M) (hh : MetricSmooth h) (S : Set M.Carrier) (hS : IsCompact S)
    (q y : M.Carrier)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ γ : IntegrableCurve h q y,
      curveLength h γ.1 < inducedDistance h q y+ε ∧ Set.MapsTo γ.1 (Set.Icc (0 : ℝ) 1) S)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (N : ℕ) (v : Fin N → M.Carrier), (∀ i, v i ∈ S) ∧
      fieldPolygonEnergy h q y v = inducedDistance h q y^2 ∧
      (∀ w : Fin N → M.Carrier, fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w) ∧
      ∀ i : Fin (N+1), inducedDistance h (fieldPolygonPoint q y v i.castSucc)
        (fieldPolygonPoint q y v i.succ) < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (inducedDistance h q y^2/δ^2)
  have hδsq : 0 < δ^2 := sq_pos_of_pos hδ
  have Hlarge : inducedDistance h q y^2 < (N+1 : ℕ)*δ^2 := by
    have H := (div_lt_iff₀ hδsq).mp hN
    have Hδ := mul_pos (show (0 : ℝ) < 1 by norm_num) hδsq
    push_cast
    linarith
  obtain ⟨v,hv,heq,hmin⟩ := exists_fieldPolygonEnergy_eq_dist_sq h hh S hS q y hnear N
  refine ⟨N,v,hv,heq,hmin,?_⟩
  intro i
  let d : Fin (N+1) → ℝ := fun j => inducedDistance h
    (fieldPolygonPoint q y v j.castSucc) (fieldPolygonPoint q y v j.succ)
  have Hterm : d i^2 ≤ ∑ j, d j^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i)
  have Hmul := mul_le_mul_of_nonneg_left Hterm (show (0 : ℝ) ≤ (N+1 : ℕ) by positivity)
  have Hbound : (N+1 : ℕ)*d i^2 < (N+1 : ℕ)*δ^2 := Hmul.trans_lt (by
    change fieldPolygonEnergy h q y v < (N+1 : ℕ)*δ^2
    rw [heq]
    exact Hlarge)
  have Hsq : d i^2 < δ^2 := (mul_lt_mul_iff_right₀ (show (0 : ℝ) < (N+1 : ℕ) by positivity)).mp Hbound
  exact (sq_lt_sq₀ (inducedDistance_nonneg h hh _ _) hδ.le).mp Hsq

end Yau.LeafProofs.L23Aux
