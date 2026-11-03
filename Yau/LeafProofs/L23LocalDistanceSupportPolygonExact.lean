import Yau.LeafProofs.L23LocalDistanceSupportSamples

/-! Compact confinement of near-minimizers forces exact finite polygon energy d². -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem fieldPolygonEnergy_self (h : HermitianField M) (hh : MetricSmooth h)
    (q : M.Carrier) (N : ℕ) : fieldPolygonEnergy h q q (fun _ : Fin N => q) = 0 := by
  have Hpoint : ∀ i : Fin (N+2), fieldPolygonPoint q q (fun _ : Fin N => q) i = q := by
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    change Fin.lastCases q (fun _ : Fin N => q) j = q
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp
    · simp
  simp only [fieldPolygonEnergy,Hpoint,inducedDistance_self h hh q,zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero,mul_zero]

theorem exists_fieldPolygonEnergy_eq_dist_sq
    (h : HermitianField M) (hh : MetricSmooth h) (S : Set M.Carrier) (hS : IsCompact S)
    (q y : M.Carrier)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ γ : IntegrableCurve h q y,
      curveLength h γ.1 < inducedDistance h q y+ε ∧ Set.MapsTo γ.1 (Set.Icc (0 : ℝ) 1) S)
    (N : ℕ) :
    ∃ v : Fin N → M.Carrier, (∀ i, v i ∈ S) ∧
      fieldPolygonEnergy h q y v = inducedDistance h q y^2 ∧
      ∀ w : Fin N → M.Carrier, fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w := by
  letI := metricSpaceOfField h hh
  have hd : 0 ≤ inducedDistance h q y := inducedDistance_nonneg h hh q y
  obtain ⟨γ₀,_,hγ₀⟩ := hnear 1 zero_lt_one
  have hq : q ∈ S := by
    have H := hγ₀ (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    rwa [γ₀.1.start_eq] at H
  by_cases hzero : inducedDistance h q y = 0
  · have hqy : q = y := dist_eq_zero.mp hzero
    subst y
    refine ⟨(fun _ => q),(fun _ => hq),?_,?_⟩
    · rw [fieldPolygonEnergy_self h hh q N,inducedDistance_self h hh q]
      norm_num
    · intro w
      rw [fieldPolygonEnergy_self h hh q N]
      have H := inducedDistance_sq_le_fieldPolygonEnergy h hh q q w
      simpa only [inducedDistance_self h hh q,zero_pow (by decide : 2 ≠ 0)] using H
  have hdpos : 0 < inducedDistance h q y := lt_of_le_of_ne hd (Ne.symm hzero)
  obtain ⟨v,hv,hmin⟩ := exists_minimizing_fieldPolygonEnergy h hh S hS q y hq N
  have Hlower := inducedDistance_sq_le_fieldPolygonEnergy h hh q y v
  have Hupper : fieldPolygonEnergy h q y v ≤ inducedDistance h q y^2 := by
    by_contra! hsmall
    let E := fieldPolygonEnergy h q y v
    have hE : 0 ≤ E := (sq_nonneg _).trans Hlower
    have Hsqrt : inducedDistance h q y < Real.sqrt E := (Real.lt_sqrt hd).mpr hsmall
    let ε := (Real.sqrt E-inducedDistance h q y)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨γ,hγ,hγS⟩ := hnear ε hε
    have hγpos : 0 < curveLength h γ.1 := hdpos.trans_le (inducedDistance_le_curveLength h γ)
    obtain ⟨w,hw,hEw⟩ := exists_curve_polygon_energy_le_sq_length h hh γ hγpos S hγS N
    have Hmin := (hmin w hw).trans hEw
    have Hlt : curveLength h γ.1 < Real.sqrt E := by
      dsimp only [ε] at hγ
      linarith
    have Hsq : curveLength h γ.1 ^ 2 < E := by
      have H := (sq_lt_sq₀ hγpos.le (Real.sqrt_nonneg E)).mpr Hlt
      rwa [Real.sq_sqrt hE] at H
    exact (not_lt_of_ge Hmin) Hsq
  have Heq := le_antisymm Hupper Hlower
  refine ⟨v,hv,Heq,?_⟩
  intro w
  rw [Heq]
  exact inducedDistance_sq_le_fieldPolygonEnergy h hh q y w

end Yau.LeafProofs.L23Aux
