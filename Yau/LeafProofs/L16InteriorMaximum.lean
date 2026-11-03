import Yau.LeafProofs.L16
open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
theorem interior_linearOp_nonneg_at_max {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O)
    (hspace : ∀ p ∈ O ×ˢ Set.Ioc 0 T, ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1)
    (htime : ∀ p ∈ O ×ˢ Set.Ioc 0 T, DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc 0 T) p.2)
    (hEll : Elliptic (O ×ˢ Set.Ioc 0 T) a lam upper)
    {p : Point n} (hp : p ∈ O ×ˢ Set.Ioc 0 T)
    (hmax : IsMaxOn u (cylinder (closure O) 0 T) p) :
    0 ≤ linearOp (cylinder (closure O) 0 T) a b u p := by
  have hpQ : p ∈ cylinder (closure O) 0 T :=
    ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩
  have hsmax : IsLocalMax (fun x => u (x,p.2)) p.1 := by
    have hh : IsMaxOn (fun x => u (x,p.2)) (closure O) p.1 := by
      intro x hx
      exact hmax ⟨hx, hp.2.1.le, hp.2.2⟩
    exact hh.isLocalMax (Filter.mem_of_superset (hO.mem_nhds hp.1) subset_closure)
  have hD : spatialD u p = 0 := hsmax.fderiv_eq_zero
  have hH : ∀ v : Space n, spatialDD u p v v ≤ 0 :=
    secondFDeriv_nonpos_of_isLocalMax (hspace p hp) hsmax
  have hcontract := bilinear_contraction_nonpos Yau.realVec (spatialDD u p)
    (elliptic_posSemidef hEll hp) hH
  have hfiber : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Set.Icc 0 T := by
    ext t
    simp only [Yau.Parabolic.cylinder, Set.mem_prod, Set.mem_ofPred_eq, hpQ.1, true_and]
  have htimeDiff : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc 0 T) p.2 := by
    exact htime p hp
  have htimeMax : IsMaxOn (fun t => u (p.1,t)) (Set.Icc 0 T) p.2 := by
    intro t ht
    exact hmax ⟨hpQ.1, ht⟩
  have htime : 0 ≤ timeD (cylinder (closure O) 0 T) u p := by
    simpa only [timeD, hfiber] using
      derivWithin_nonneg_at_Icc_max hp.2.1 hp.2.2 htimeDiff htimeMax
  simp only [linearOp, hD, zero_apply, mul_zero,
    Finset.sum_const_zero, sub_zero]
  exact sub_nonneg.mpr (hcontract.trans htime)

theorem interior_strict_maximum_principle {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O))
    (hcontinuous : ContinuousOn u (cylinder (closure O) 0 T))
    (hspace : ∀ p ∈ O ×ˢ Set.Ioc 0 T, ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1)
    (htime : ∀ p ∈ O ×ˢ Set.Ioc 0 T, DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc 0 T) p.2)
    (hEll : Elliptic (O ×ˢ Set.Ioc 0 T) a lam upper)
    (hinit : ∀ x ∈ closure O, u (x,0) ≤ 0)
    (hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) ≤ 0)
    (hop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b u p < 0) :
    ∀ p ∈ cylinder (closure O) 0 T, u p ≤ 0 := by
  intro p hp
  by_contra hn
  have hpos : 0 < u p := lt_of_not_ge hn
  obtain ⟨q, hq, hmax⟩ := (hcompact.prod isCompact_Icc).exists_isMaxOn ⟨p, hp⟩ hcontinuous
  have hposq : 0 < u q := hpos.trans_le (hmax hp)
  have hqO : q.1 ∈ O := by
    by_contra hnot
    have hfr : q.1 ∈ frontier O :=
      ⟨hq.1, by simpa only [hO.interior_eq] using hnot⟩
    exact not_lt_of_ge (hlat q.1 hfr q.2 hq.2) hposq
  have hqt : 0 < q.2 := by
    by_contra hnot
    have hz : q.2 = 0 := le_antisymm (le_of_not_gt hnot) hq.2.1
    have hh := hinit q.1 hq.1
    have heq : (q.1, (0 : ℝ)) = q := Prod.ext rfl hz.symm
    rw [heq] at hh
    exact not_lt_of_ge hh hposq
  have hq' : q ∈ O ×ˢ Set.Ioc 0 T := ⟨hqO, hqt, hq.2.2⟩
  exact not_lt_of_ge (interior_linearOp_nonneg_at_max hO hspace htime hEll hq' hmax) (hop q hq')


/-- The time tilt uses derivatives only at the evaluated interior point. -/
theorem interior_linearOp_sub_timeAffine {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hT : 0 < T) {p : Point n}
    (htime : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc 0 T) p.2)
    (δ : ℝ) (hp : p ∈ O ×ˢ Set.Ioc 0 T) :
    linearOp (cylinder (closure O) 0 T) a b (fun z => u z - δ*(z.2+1)) p =
      linearOp (cylinder (closure O) 0 T) a b u p - δ := by
  have hfiber : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder, subset_closure hp.1]
  have hc : HasDerivAt (fun t : ℝ => δ*(t+1)) δ p.2 := by
    convert ((hasDerivAt_id p.2).add_const 1).const_mul δ using 1 <;> simp
  have ht : timeD (cylinder (closure O) 0 T) (fun z => u z-δ*(z.2+1)) p =
      timeD (cylinder (closure O) 0 T) u p-δ := by
    simp only [timeD, hfiber]
    rw [derivWithin_fun_sub htime hc.differentiableAt.differentiableWithinAt]
    rw [hc.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.2 ⟨hp.2.1.le,hp.2.2⟩)]
  simp only [linearOp, spatialD_sub_timeAffine, spatialDD_sub_timeAffine, ht]
  ring
theorem interior_maximum_principle {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hcontinuous : ContinuousOn u (cylinder (closure O) 0 T))
    (hspace : ∀ p ∈ O ×ˢ Set.Ioc 0 T, ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1)
    (htime : ∀ p ∈ O ×ˢ Set.Ioc 0 T, DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc 0 T) p.2)
    (hEll : Elliptic (O ×ˢ Set.Ioc 0 T) a lam upper)
    (hinit : ∀ x ∈ closure O, u (x,0) ≤ 0)
    (hlat : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) ≤ 0)
    (hop : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b u p ≤ 0) :
    ∀ p ∈ cylinder (closure O) 0 T, u p ≤ 0 := by
  intro p hp
  by_contra hn
  have hpos : 0 < u p := lt_of_not_ge hn
  have hpt : 0 < p.2+1 := by linarith [hp.2.1]
  let δ : ℝ := u p / (2*(p.2+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ*(p.2+1) = u p / 2 := by
    dsimp [δ]
    field_simp
  have hcontinuousTilt : ContinuousOn (fun z => u z - δ*(z.2+1))
      (cylinder (closure O) 0 T) := hcontinuous.sub (by fun_prop)
  have hspaceTilt : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      ContDiffAt ℝ 2 (fun x => u (x,p.2)-δ*(p.2+1)) p.1 := by
    intro p hp
    exact (hspace p hp).sub contDiffAt_const
  have htimeTilt : ∀ p ∈ O ×ˢ Set.Ioc 0 T,
      DifferentiableWithinAt ℝ (fun t => u (p.1,t)-δ*(t+1)) (Set.Icc 0 T) p.2 := by
    intro p hp
    exact (htime p hp).sub (by fun_prop)
  have hinit' : ∀ x ∈ closure O, u (x,0) - δ*((0 : ℝ)+1) ≤ 0 := by
    intro x hx
    have := hinit x hx
    simp only [zero_add, mul_one]
    linarith
  have hlat' : ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T,
      u (x,t) - δ*(t+1) ≤ 0 := by
    intro x hx t ht
    have := hlat x hx t ht
    have hmul : 0 ≤ δ*(t+1) := mul_nonneg hδ.le (by linarith [ht.1])
    linarith
  have hop' : ∀ z ∈ O ×ˢ Set.Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) a b (fun z => u z - δ*(z.2+1)) z < 0 := by
    intro z hz
    rw [interior_linearOp_sub_timeAffine hT (htime z hz) δ hz]
    linarith [hop z hz]
  have hh := interior_strict_maximum_principle hO hcompact hcontinuousTilt hspaceTilt htimeTilt hEll hinit' hlat' hop' p hp
  rw [hδeq] at hh
  linarith


end Yau.LeafProofs.L16Aux
