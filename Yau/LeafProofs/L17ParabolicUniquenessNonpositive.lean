import Yau.LeafProofs.L17ParabolicUniquenessMaximum

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicUniquenessAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}

theorem dampedTime_nonneg_of_maximum (u : SchauderSpace P T gamma hT)
    (x : M.Carrier) (t : Time T) (ht : 0 < (t : ℝ)) (b : ℝ)
    (hmax : IsMaxOn (fun tau => damped u (closedTimePath T hT x tau)-b)
      (Icc (0 : ℝ) T) (t : ℝ)) : 0 ≤ dampedTime u (x,t) := by
  have hd : HasDerivWithinAt (fun tau => damped u (closedTimePath T hT x tau)-b)
      (dampedTime u (x,t)) (Icc (0 : ℝ) T) (t : ℝ) := by
    apply ((damped_hasDerivWithinAt u x t).sub_const b).congr
    · intro tau htau
      dsimp only [damped,closedTimePath]
      rw [projIcc_of_mem hT.le htau]
    · dsimp only [damped,closedTimePath]
      rw [projIcc_val]
  have hh := L16Aux.derivWithin_nonneg_at_Icc_max ht t.property.2
    hd.differentiableWithinAt hmax
  rwa [hd.derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property)] at hh

/-- The global supremum is only approximated. Attainment is needed solely
on one compact coordinate cylinder, where the actual local derivatives apply. -/
theorem damped_nonpositive (u : SchauderSpace P T gamma hT)
    (hu : ∀ q : Cylinder M T,
      timeFun u q-laplacian g (fun y => schauderFun u (y,q.2)) q.1 = 0) :
    ∀ q, damped u q ≤ 0 := by
  classical
  intro q
  by_contra hq
  have hqpos : 0 < damped u q := lt_of_not_ge hq
  have hb : BddAbove (range (damped u)) := by
    refine ⟨P.radius^2*‖u‖,?_⟩
    rintro a ⟨q',rfl⟩
    exact (le_abs_self _).trans (damped_abs_le u q')
  let m : ℝ := sSup (range (damped u))
  have hupp : ∀ q', damped u q' ≤ m := fun q' => le_csSup hb ⟨q',rfl⟩
  have hm : 0 < m := hqpos.trans_le (hupp q)
  let N : ℝ := Fintype.card (RIdx n)
  let D : ℝ := 4*N*(P.charts.bound 0/4)/P.radius^2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hC : 0 < P.charts.bound 0 := P.charts.bound_pos 0
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨eps,heps,hem,heD⟩ := exists_positive_epsilon hm hD
  have hemlt : eps < m := by linarith
  have hne : (range (damped u)).Nonempty := ⟨damped u q,⟨q,rfl⟩⟩
  obtain ⟨a,⟨⟨p,tstar⟩,rfl⟩,hneara⟩ :=
    exists_lt_of_lt_csSup hne (show m-eps < sSup (range (damped u)) by dsimp [m]; linarith)
  obtain ⟨z,t,hz,ht,hbig,hsp,htm⟩ :=
    exists_penalized_maximum (P := P) (hT := hT) (damped u) (damped_continuous u)
      (damped_initial u) heps hemlt hupp p tstar hneara
  have hzA : z ∈ ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) hz
  have hzs : z ∈ (P.charts.chart p).source :=
    P.charts.closedBall_source p (ball_subset_closedBall hzA)
  let a := scalarSymbol (pullbackMatrix g (P.charts.chart p) z)
  have ha : a.PosSemidef := (scalarSymbol_posDef
    (pullbackMatrix_posDef g (P.charts.chart p) (P.charts.differentiable p)
      (P.charts.inverse_differentiable p) hzs)).posSemidef
  let k := 2*eps/P.radius^2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hspace : realHessianContraction a (fun y => damped u (P.charts.chart p y,t)) z ≤
      2*k*(∑ i, a i i) :=
    contraction_penalized_nonpos (damped_background_contDiffAt u p t hzs) k a ha hsp
  have htrace : (∑ i, a i i) ≤ N*(P.charts.bound 0/4) :=
    symbol_trace_le P.charts p hzA
  have hnum : 2*k*(N*(P.charts.bound 0/4)) = D*eps := by
    dsimp [k,D]
    ring
  have hspace' : realHessianContraction a (fun y => damped u (P.charts.chart p y,t)) z ≤ D*eps := by
    calc
      _ ≤ 2*k*(∑ i, a i i) := hspace
      _ ≤ 2*k*(N*(P.charts.bound 0/4)) := mul_le_mul_of_nonneg_left htrace (by positivity)
      _ = _ := hnum
  have htime : 0 ≤ dampedTime u (P.charts.chart p z,t) :=
    dampedTime_nonneg_of_maximum u _ t ht (k*‖z‖^2) htm
  have heq := damped_equation u hu p t hzs
  change dampedTime u (P.charts.chart p z,t)-
    realHessianContraction a (fun y => damped u (P.charts.chart p y,t)) z =
      -damped u (P.charts.chart p z,t) at heq
  have hp : 0 ≤ k*‖z‖^2 := mul_nonneg hk (sq_nonneg _)
  change m-eps < damped u (P.charts.chart p z,t)-k*‖z‖^2 at hbig
  linarith

end Yau.LeafProofs.L17ParabolicUniquenessAux
