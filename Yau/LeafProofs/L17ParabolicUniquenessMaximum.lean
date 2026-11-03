import Yau.LeafProofs.L17ParabolicUniquenessDamping

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicUniquenessAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T : ℝ} {hT : 0 < T}

theorem exists_positive_epsilon {m D : ℝ} (hm : 0 < m) (hD : 0 ≤ D) :
    ∃ eps : ℝ, 0 < eps ∧ eps < m/4 ∧ D*eps < m/2 := by
  refine ⟨m/(8*(1+D)), div_pos hm (by positivity), ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 8*(1+D))).mpr
    nlinarith
  · have he : m/(8*(1+D))*(8*(1+D)) = m := div_mul_cancel₀ _ (by positivity)
    have hepos : 0 < m/(8*(1+D)) := div_pos hm (by positivity)
    nlinarith

/-- A near supremum gives a genuine positive maximum in one original chart.
The spatial maximum is interior; the time maximum includes the terminal face. -/
theorem exists_penalized_maximum
    (v : Cylinder M T → ℝ) (hv : Continuous v)
    (hv0 : ∀ x, v (x,⟨0,⟨le_rfl,hT.le⟩⟩) = 0)
    {m eps : ℝ} (heps : 0 < eps) (hem : eps < m)
    (hupper : ∀ q, v q ≤ m) (p : M.Carrier) (tstar : Time T)
    (hnear : m-eps < v (p,tstar)) :
    ∃ (z : ComplexVector n) (t : Time T),
      z ∈ ball 0 P.radius ∧ 0 < (t : ℝ) ∧
      m-eps < v (P.charts.chart p z,t)-(2*eps/P.radius^2)*‖z‖^2 ∧
      IsLocalMax (fun y => v (P.charts.chart p y,t)-(2*eps/P.radius^2)*‖y‖^2) z ∧
      IsMaxOn (fun tau => v (closedTimePath T hT (P.charts.chart p z) tau)-
        (2*eps/P.radius^2)*‖z‖^2) (Icc (0 : ℝ) T) (t : ℝ) := by
  classical
  let k := 2*eps/P.radius^2
  let Q : Set (ComplexVector n × Time T) := closedBall 0 P.radius ×ˢ univ
  let f : ComplexVector n × Time T → ℝ :=
    fun q => v (P.charts.chart p q.1,q.2)-k*‖q.1‖^2
  have hsource : closedBall (0 : ComplexVector n) P.radius ⊆ (P.charts.chart p).source :=
    (closedBall_subset_closedBall P.radius_lt.le).trans (P.charts.closedBall_source p)
  have hc : ContinuousOn (P.charts.chart p) (closedBall 0 P.radius) :=
    (P.charts.chart p).continuousOn.mono hsource
  have hmap : ContinuousOn (fun q : ComplexVector n × Time T => (P.charts.chart p q.1,q.2)) Q :=
    hc.prodMap continuousOn_id
  have hf : ContinuousOn f Q :=
    (hv.comp_continuousOn hmap).sub
      (((continuous_fst.norm.pow 2).const_mul k).continuousOn)
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_univ
  have hzero : (0 : ComplexVector n) ∈ closedBall 0 P.radius := by
    simpa using P.radius_pos.le
  obtain ⟨⟨z,t⟩,hzt,hmax⟩ := hQ.exists_isMaxOn ⟨(0,tstar),hzero,mem_univ _⟩ hf
  have hzle : ‖z‖ ≤ P.radius := by simpa using hzt.1
  have hcenter : m-eps < f (z,t) := by
    have hh := hmax (show (0,tstar) ∈ Q from ⟨hzero,mem_univ _⟩)
    change f (0,tstar) ≤ f (z,t) at hh
    have hval : f (0,tstar) = v (p,tstar) := by simp [f,P.charts.center]
    rw [hval] at hh
    exact hnear.trans_le hh
  have hkp : 0 ≤ k := by dsimp [k]; positivity
  have hz : z ∈ ball (0 : ComplexVector n) P.radius := by
    rw [mem_ball_zero_iff]
    by_contra hn
    have he : ‖z‖ = P.radius := le_antisymm hzle (le_of_not_gt hn)
    have hk : k*‖z‖^2 = 2*eps := by
      rw [he]
      dsimp [k]
      exact div_mul_cancel₀ _ (pow_ne_zero _ P.radius_pos.ne')
    have hh := hupper (P.charts.chart p z,t)
    change m-eps < v (P.charts.chart p z,t)-k*‖z‖^2 at hcenter
    rw [hk] at hcenter
    linarith
  have ht : 0 < (t : ℝ) := by
    by_contra hn
    have ht0 : t = ⟨0,⟨le_rfl,hT.le⟩⟩ := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
    subst t
    have hh := hv0 (P.charts.chart p z)
    change m-eps < v (P.charts.chart p z,⟨0,⟨le_rfl,hT.le⟩⟩)-k*‖z‖^2 at hcenter
    rw [hh] at hcenter
    have hk0 : 0 ≤ k*‖z‖^2 := mul_nonneg hkp (sq_nonneg _)
    linarith
  refine ⟨z,t,hz,ht,hcenter,?_,?_⟩
  · have hs : IsMaxOn (fun y => v (P.charts.chart p y,t)-k*‖y‖^2)
        (closedBall 0 P.radius) z := by
      intro y hy
      change f (y,t) ≤ f (z,t)
      exact hmax (show (y,t) ∈ Q from ⟨hy,mem_univ _⟩)
    exact hs.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  · intro tau htau
    have hh := hmax (show (z,projIcc (0 : ℝ) T hT.le tau) ∈ Q from ⟨hzt.1,mem_univ _⟩)
    change f (z,projIcc (0 : ℝ) T hT.le tau) ≤ f (z,t) at hh
    change v (P.charts.chart p z,projIcc (0 : ℝ) T hT.le tau)-k*‖z‖^2 ≤
      v (P.charts.chart p z,projIcc (0 : ℝ) T hT.le (t : ℝ))-k*‖z‖^2
    simpa only [f,projIcc_val] using hh

end Yau.LeafProofs.L17ParabolicUniquenessAux
