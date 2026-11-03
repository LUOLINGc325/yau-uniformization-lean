import Yau.LeafProofs.L23LocalDistanceSupportPartition

/-! Equal actual-length samples yield finite polygon energy below curve length squared. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem monotoneOn_curveLengthPrimitive
    (h : HermitianField M) {q y : M.Carrier} (γ : IntegrableCurve h q y) :
    MonotoneOn (fun t => ∫ u in (0 : ℝ)..t, curveSpeed h γ.1 u) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have HI : IntervalIntegrable (curveSpeed h γ.1) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hb.1).mpr
      (γ.2.mono_set (Set.Icc_subset_Icc le_rfl hb.2))
  exact intervalIntegral.integral_mono_interval le_rfl ha.1 hab
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _) HI

theorem curveLengthPrimitive_sub_eq_integral
    (h : HermitianField M) {q y : M.Carrier} (γ : IntegrableCurve h q y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ u in (0 : ℝ)..b, curveSpeed h γ.1 u)-(∫ u in (0 : ℝ)..a, curveSpeed h γ.1 u) =
      ∫ u in Set.Icc a b, curveSpeed h γ.1 u := by
  have HIa : IntervalIntegrable (curveSpeed h γ.1) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha).mpr
      (γ.2.mono_set (Set.Icc_subset_Icc le_rfl (hab.trans hb)))
  have HIab : IntervalIntegrable (curveSpeed h γ.1) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (γ.2.mono_set (Set.Icc_subset_Icc ha hb))
  have H := intervalIntegral.integral_add_adjacent_intervals HIa HIab
  rw [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc] at H
  linarith

theorem exists_curve_polygon_energy_le_sq_length
    (h : HermitianField M) (hh : MetricSmooth h) {q y : M.Carrier} (γ : IntegrableCurve h q y)
    (hpos : 0 < curveLength h γ.1) (S : Set M.Carrier)
    (himage : Set.MapsTo γ.1 (Set.Icc (0 : ℝ) 1) S) (N : ℕ) :
    ∃ v : Fin N → M.Carrier, (∀ i, v i ∈ S) ∧
      fieldPolygonEnergy h q y v ≤ curveLength h γ.1 ^ 2 := by
  let L : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, curveSpeed h γ.1 u
  have hLzero : L 0 = 0 := by simp [L]
  have hLone : L 1 = curveLength h γ.1 := by
    change (∫ u in (0 : ℝ)..1, curveSpeed h γ.1 u) = curveLength h γ.1
    rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
    rfl
  have hLpos : 0 < L 1 := by rw [hLone]; exact hpos
  obtain ⟨t,ht₀,ht₁,hti,htmono,htL⟩ := exists_equal_primitive_samples L
    (continuousOn_curveLengthPrimitive h γ) (monotoneOn_curveLengthPrimitive h γ) hLzero hLpos N
  let v : Fin N → M.Carrier := fun i => γ.1 (t i.castSucc.succ)
  have hpoints : ∀ i : Fin (N+2), fieldPolygonPoint q y v i = γ.1 (t i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change q = γ.1 (t 0)
      rw [ht₀,γ.1.start_eq]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · have Hlast : (Fin.last N).succ = Fin.last (N+1) := rfl
        rw [Hlast,ht₁,γ.1.finish_eq]
        change Fin.lastCases y v (Fin.last N) = y
        simp
      · simp only [fieldPolygonPoint,Fin.cases_succ,Fin.lastCases_castSucc]
        rfl
  have hN : (0 : ℝ) < (N+1 : ℕ) := by positivity
  have hedge (i : Fin (N+1)) : inducedDistance h
      (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ) ≤
        curveLength h γ.1/(N+1 : ℕ) := by
    rw [hpoints,hpoints]
    have htij : t i.castSucc ≤ t i.succ := (htmono (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
    have H := inducedDistance_curve_segment_le_integral h hh γ (hti i.castSucc).1 htij (hti i.succ).2
    rw [← curveLengthPrimitive_sub_eq_integral h γ (hti i.castSucc).1 htij (hti i.succ).2] at H
    have Hint : L (t i.succ)-L (t i.castSucc) = curveLength h γ.1/(N+1 : ℕ) := by
      rw [htL,htL,hLone]
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      ring
    exact H.trans_eq Hint
  refine ⟨v,(fun i => himage (hti i.castSucc.succ)),?_⟩
  have Hsum : (∑ i : Fin (N+1), inducedDistance h
      (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)^2) ≤
      ∑ _i : Fin (N+1), (curveLength h γ.1/(N+1 : ℕ))^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (inducedDistance_nonneg h hh _ _) (div_nonneg hpos.le hN.le)).mpr (hedge i)
  have H := mul_le_mul_of_nonneg_left Hsum hN.le
  apply H.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [hN.ne']
  <;> ring

end Yau.LeafProofs.L23Aux
