import Yau.Proofs.P06CylinderRegularityHodgeEquation
import Yau.Proofs.P06CylinderRegularityCoefficientBounds
import Yau.Proofs.P06CylinderRegularityHeatFlux

/-! Actual fixed compact extensions and ellipticity data for a chart
cylinder. They are selected before any heat solution or cutoff index. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Parabolic Yau.LeafProofs.L03 Yau.LeafProofs.L16Aux

theorem hodgeCoordinate_joint_contDiffOn {n k : ℕ} {M : ComplexManifold n}
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0))
    (x : M.Carrier) {α : Type} [Fintype α]
    (b : Basis α ℝ (HodgeJets.Fiber n k)) (r : α) :
    ContDiffOn ℝ ∞ (fun p : Point n => hodgeRegularityCoord b (U p.2) x p.1 r)
      (chartTarget x ×ˢ Set.Ioi 0) := by
  have hModel : ContDiffOn ℝ ∞ (fun p : Point n => chartForm (U p.2) x p.1)
      (chartTarget x ×ˢ Set.Ioi 0) :=
    (modelForm_contDiffOn_iff _ _).mpr (fun I => by
      simpa only [chartForm_apply_basis] using hU x I)
  exact (b.coord r).toContinuousLinearMap.contDiff.comp_contDiffOn hModel

theorem exists_chart_heat_coefficients {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {α : Type} [Fintype α] [DecidableEq α]
    (b : Basis α ℝ (HodgeJets.Fiber n k)) {Q : Set (Point n)}
    (hcQ : IsCompact (closure Q)) (hQO : ∀ p ∈ closure Q, p.1 ∈ chartTarget x) :
    ∃ (q : RIdx n → RIdx n → Point n → ℝ)
      (e1 : α → α → RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
      (lam upper A : ℝ), 0 < lam ∧ 0 ≤ A ∧
      (∀ i j, ContDiff ℝ ∞ (q i j) ∧ HasCompactSupport (q i j)) ∧
      (∀ r c i, ContDiff ℝ ∞ (e1 r c i) ∧ HasCompactSupport (e1 r c i)) ∧
      (∀ r c, ContDiff ℝ ∞ (e0 r c) ∧ HasCompactSupport (e0 r c)) ∧
      Elliptic Q (heatPrincipal q) lam upper ∧
      (∀ p ∈ Q, ∀ i j, |heatPrincipal q p i j| ≤ A) ∧
      (∀ p ∈ Q, ∀ i j, q i j p = hodgeRegularityQ g.form x i j p.1) ∧
      (∀ p ∈ Q, ∀ r c i, e1 r c i p = hodgeRegularityE1 g.form x b r c i p.1) ∧
      (∀ p ∈ Q, ∀ r c, e0 r c p = hodgeRegularityE0 g.form x b r c p.1) := by
  classical
  let O : Set (Point n) := chartTarget x ×ˢ Set.univ
  have hO : IsOpen O := (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hQO' : closure Q ⊆ O := fun p hp => ⟨hQO p hp,Set.mem_univ _⟩
  obtain ⟨θ,hθ,hNear⟩ := exists_test_eq_one_near_compact hO hcQ hQO'
  let q : RIdx n → RIdx n → Point n → ℝ := fun i j p => θ p * hodgeRegularityQ g.form x i j p.1
  let e1 : α → α → RIdx n → Point n → ℝ := fun r c i p => θ p * hodgeRegularityE1 g.form x b r c i p.1
  let e0 : α → α → Point n → ℝ := fun r c p => θ p * hodgeRegularityE0 g.form x b r c p.1
  have hq (i j : RIdx n) : ContDiff ℝ ∞ (q i j) ∧ HasCompactSupport (q i j) :=
    cutoff_contDiff hO hθ.1 hθ.2.1 hθ.2.2
      ((hodgeRegularityQ_contDiffOn g x i j).comp contDiffOn_fst (fun p hp => hp.1))
  have he1 (r c : α) (i : RIdx n) : ContDiff ℝ ∞ (e1 r c i) ∧ HasCompactSupport (e1 r c i) :=
    cutoff_contDiff hO hθ.1 hθ.2.1 hθ.2.2
      ((hodgeRegularityE1_contDiffOn g x b r c i).comp contDiffOn_fst (fun p hp => hp.1))
  have he0 (r c : α) : ContDiff ℝ ∞ (e0 r c) ∧ HasCompactSupport (e0 r c) :=
    cutoff_contDiff hO hθ.1 hθ.2.1 hθ.2.2
      ((hodgeRegularityE0_contDiffOn g x b r c).comp contDiffOn_fst (fun p hp => hp.1))
  have hOne (p : Point n) (hp : p ∈ Q) : θ p = 1 := (hNear p (subset_closure hp)).eq_of_nhds
  have hqEq : ∀ p ∈ Q, ∀ i j, q i j p = hodgeRegularityQ g.form x i j p.1 := by
    intro p hp i j
    simp only [q,hOne p hp,one_mul]
  have he1Eq : ∀ p ∈ Q, ∀ r c i, e1 r c i p = hodgeRegularityE1 g.form x b r c i p.1 := by
    intro p hp r c i
    simp only [e1,hOne p hp,one_mul]
  have he0Eq : ∀ p ∈ Q, ∀ r c, e0 r c p = hodgeRegularityE0 g.form x b r c p.1 := by
    intro p hp r c
    simp only [e0,hOne p hp,one_mul]
  obtain ⟨A,hA,hBound⟩ := finite_global_abs_bound
    (fun ij : RIdx n × RIdx n => fun p => heatPrincipal q p ij.1 ij.2)
    (fun ij => ((hq ij.1 ij.2).1.div_const 2).continuous)
    (fun ij => (hq ij.1 ij.2).2.comp_left (g := fun s : ℝ => s/2) (by norm_num))
  have hImg : IsCompact (Prod.fst '' closure Q) := hcQ.image continuous_fst
  have hImgO : Prod.fst '' closure Q ⊆ chartTarget x := by
    rintro z ⟨p,hp,rfl⟩
    exact hQO p hp
  obtain ⟨ell,hell,hLower⟩ := hodgeRegularityQ_uniform_coercive g x hImg hImgO
  let lam := ell/2
  let upper := max lam ((Fintype.card (RIdx n) : ℝ)*A)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  refine ⟨q,e1,e0,lam,upper,A,hlam,hA,hq,he1,he0,?_,
    fun p _ i j => hBound (i,j) p,hqEq,he1Eq,he0Eq⟩
  refine ⟨hlam,le_max_left _ _,?_⟩
  intro p hp
  refine ⟨?_,?_⟩
  · apply Matrix.ext
    intro i j
    change q j i p/2 = q i j p/2
    rw [hqEq p hp, hqEq p hp, hodgeRegularityQ_symm g.form x j i]
  · intro v
    have hL := hLower p.1 (Set.mem_image_of_mem Prod.fst (subset_closure hp)) v
    have hQuad : (∑ i, ∑ j, heatPrincipal q p i j * v i * v j) =
        (∑ i, ∑ j, hodgeRegularityQ g.form x i j p.1 * v j * v i)/2 := by
      simp only [heatPrincipal,hqEq p hp,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨?_,?_⟩
    · rw [hQuad]
      dsimp only [lam]
      nlinarith only [hL]
    · have hUpper := quadratic_upper_bound (fun i j => heatPrincipal q p i j) hA
        (fun i j => hBound (i,j) p) v
      exact hUpper.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Finset.sum_nonneg fun i _ => sq_nonneg (v i)))

end Yau.NodeProofs.P06Aux.CylinderReg
