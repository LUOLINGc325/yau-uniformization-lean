import Yau.Proofs.F05HolderFixedData
import Yau.Proofs.F05HolderCoefficientSource
import Yau.Proofs.F05HolderEquationRestriction
import Yau.Proofs.F05HolderInitialBarrier
import Yau.LeafProofs.L16ExpBoundaryReduction

/-! Actual logarithmic error controls on a physical model chart. The
transform and every numerical bound are fixed before the endpoint and q;
zero trace is required only on the true physical face and the initial face. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryAux Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

def F05BufferedLogControl (k : Option (RIdx n)) (T ν upper A₀ b₀ H W₀ : ℝ)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ) : Prop :=
  ContinuousOn u (cylinder (region k 2) 0 T) ∧
  (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1) ∧
  (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2) ∧
  Elliptic (F05CapOpen k 2 ×ˢ Ioo 0 T) a ν upper ∧
  (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T, ∀ i j, |a z i j| ≤ A₀) ∧
  (∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T, ∀ i, |b z i| ≤ b₀) ∧
  (∀ x ∈ region k 2, u (x,0) = 0) ∧
  (∀ x ∈ frontier (F05FlatOpen k) ∩ Metric.ball 0 2, ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
  (∀ z ∈ cylinder (region k 2) 0 T, |u z| ≤ W₀) ∧
  ∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T,
    |linearOp (cylinder (region k 2) 0 T) a b u z| ≤ H

theorem F05_log_model_control (k : Option (RIdx n)) {S lam upper m B : ℝ}
    (hm : 0 < m) (hmB : m ≤ B)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R p : Point n → ℝ}
    (hab : SmoothCoefficients (Metric.ball 0 3 ×ˢ Icc 0 S) a b)
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc 0 S))
    (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Icc 0 S))
    (he : Elliptic (cylinder (Metric.closedBall 0 2) 0 S) a lam upper) :
    ∃ (ℓ : ℝ → ℝ) (A₁ b₁ H W₀ E L : ℝ),
      0 < A₁ ∧ 0 < b₁ ∧ 0 < H ∧ 0 < W₀ ∧ 0 < E ∧ 0 < L ∧
      (∀ z ∈ cylinder (Metric.closedBall (0 : Space n) 2) 0 S,
        ∀ w ∈ cylinder (Metric.closedBall (0 : Space n) 2) 0 S,
        |Real.exp (ℓ (p z))-Real.exp (ℓ (p w))| ≤ L*(‖z.1-w.1‖+|z.2-w.2|)) ∧
      ∀ (T : ℝ), 0 < T → T ≤ S → ∀ q : Point n → ℝ,
      C2 (cylinder (region k 2) 0 T) q →
      (∀ z ∈ cylinder (region k 2) 0 T, m ≤ q z ∧ q z ≤ B) →
      (∀ x ∈ region k 2, q (x,0) = p (x,0)) →
      (∀ x ∈ frontier (F05FlatOpen k) ∩ Metric.ball 0 2,
        ∀ t ∈ Icc 0 T, q (x,t) = p (x,t)) →
      ExpDivergenceEquation (F05CapOpen k 3 ×ˢ Ioc 0 T) a b R q →
      F05BufferedLogControl k T (lam/B) (upper/m) A₁ b₁ H W₀
        (fun z => (q z)⁻¹ • a z) (fun z j => b z j/q z)
        (fun z => Real.log (q z)-ℓ (p z)) ∧
      ∀ z ∈ cylinder (region k 2) 0 T,
        |q z-Real.exp (ℓ (p z))| ≤ E*|Real.log (q z)-ℓ (p z)| := by
  classical
  obtain ⟨ℓ,P₀,P₁,P₂,L,hℓ,hSupport,hEq,hP₀,hP₁,hP₂,hL,h₀,h₁,h₂,hLip⟩ :=
    F05_clipped_log_ball_data hm hmB hp
  let K : Set (Point n) := Metric.closedBall 0 2 ×ˢ Icc 0 S
  let U : Set (Point n) := Metric.ball 0 2 ×ˢ Ioo 0 S
  have hKU : K ⊆ Metric.ball (0 : Space n) 3 ×ˢ Icc 0 S := fun _ hz =>
    ⟨Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3) hz.1,hz.2⟩
  have hUK : U ⊆ K := fun _ hz => ⟨Metric.ball_subset_closedBall hz.1,Ioo_subset_Icc_self hz.2⟩
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  have hP := hℓ.comp_contDiffOn (hp.mono hKU)
  obtain ⟨A₀,b₀,R₀,hA₀,hb₀,hR₀,hA,hb,hRF⟩ := F05_compact_coefficient_source_bounds
    ((isCompact_closedBall (0 : Space n) 2).prod isCompact_Icc)
    ⟨hab.1.mono hKU,fun i => (hab.2 i).mono hKU⟩ (hR.mono hKU)
  let H := 1+(1+1/m)*R₀+P₁+(∑ _i : RIdx n, ∑ _j : RIdx n, (A₀/m)*P₂)+
    ∑ _i : RIdx n, (b₀/m)*P₁
  have hH : 0 < H := by dsimp [H]; positivity
  let W₀ := 1+|Real.log m|+|Real.log B|+P₀
  have hW₀ : 0 < W₀ := by dsimp [W₀]; positivity
  let E := Real.exp (max (|Real.log m|+|Real.log B|) P₀)
  refine ⟨ℓ,A₀/m,b₀/m,H,W₀,E,L,by positivity,by positivity,hH,hW₀,
    Real.exp_pos _,hL,hLip,?_⟩
  intro T hT hTS q hq hbound hi hl heq
  let P : Point n → ℝ := fun z => ℓ (p z)
  let w : Point n → ℝ := fun z => Real.log (q z)-P z
  let A : Point n → Mat n := fun z => (q z)⁻¹ • a z
  let β : Point n → RIdx n → ℝ := fun z j => b z j/q z
  have hQK : cylinder (region k 2) 0 T ⊆ K := fun _ hz =>
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.1,
      hz.2.1,hz.2.2.trans hTS⟩
  have hOpenQ : F05CapOpen k 2 ×ˢ Ioo 0 T ⊆ cylinder (region k 2) 0 T :=
    fun _ hz => ⟨F05CapOpen_closure_subset k 2 (subset_closure hz.1),Ioo_subset_Icc_self hz.2⟩
  have hOpenU : F05CapOpen k 2 ×ˢ Ioo 0 T ⊆ U :=
    fun _ hz => ⟨hz.1.2,hz.2.1,hz.2.2.trans_le hTS⟩
  have hClosedQ : cylinder (closure (F05CapOpen k 2)) 0 T ⊆ cylinder (region k 2) 0 T :=
    fun _ hz => ⟨F05CapOpen_closure_subset k 2 hz.1,hz.2⟩
  have hqCap := c2_cylinder_mono_space (F05CapOpen_closure_subset k 2) hq
  have hPCap := hP.mono (hClosedQ.trans hQK)
  have hlow : ∀ z ∈ cylinder (region k 2) 0 T, m ≤ q z := fun z hz => (hbound z hz).1
  have hwc : ContinuousOn w (cylinder (region k 2) 0 T) :=
    log_error_continuous hm hq.1 (hP.continuousOn.mono hQK) hlow
  have hwreg := log_error_interior_regularity (F05CapOpen_isOpen k 2) hm hqCap hPCap
    (fun z hz => hlow z (hClosedQ hz))
  have hEll := elliptic_div_of_bounds
    (show Elliptic (cylinder (region k 2) 0 T) a lam upper from
      ⟨he.1,he.2.1,fun z hz => he.2.2 z (hQK hz)⟩) hm hmB hbound
  have hEllU : Elliptic (F05CapOpen k 2 ×ˢ Ioo 0 T) A (lam/B) (upper/m) :=
    ⟨hEll.1,hEll.2.1,fun z hz => hEll.2.2 z (hOpenQ hz)⟩
  have hEqPoint (z : Point n) (hz : z ∈ cylinder (region k 2) 0 T)
      (hAt : q z = p z) : ℓ (p z) = Real.log (q z) := by
    rw [← hAt]
    apply hEq
    constructor <;> linarith [(hbound z hz).1,(hbound z hz).2]
  have hop : ∀ z ∈ F05CapOpen k 2 ×ˢ Ioo 0 T,
      |linearOp (cylinder (region k 2) 0 T) A β w z| ≤ H := by
    intro z hz
    have hzU := hOpenU hz
    have hzQ := hOpenQ hz
    have hPAt : ContDiffAt ℝ 2 P z :=
      ((hP.mono hUK).contDiffAt (hU.mem_nhds hzU)).of_le (by simp)
    have hPtime : DifferentiableAt ℝ (fun t => P (z.1,t)) z.2 :=
      DifferentiableAt.comp (g := P) (f := fun t : ℝ => (z.1,t)) z.2
        (hPAt.differentiableAt (by norm_num))
        ((differentiableAt_const z.1).prodMk differentiableAt_id)
    have hzCap : z.1 ∈ closure (F05CapOpen k 2) := subset_closure hz.1
    have htP : |timeD (cylinder (closure (F05CapOpen k 2)) 0 T) P z| ≤ P₁ := by
      rw [timeD_closed_eq_deriv hT hzCap (Ioo_subset_Icc_self hz.2) hPtime,
        test_timeDerivative_eq_joint_fderiv (φ := P) (hPAt.differentiableAt (by norm_num))]
      have heₜ : ‖((0 : Space n),(1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
      have hh : |fderiv ℝ P z (0,1)| ≤ ‖fderiv ℝ P z‖ := by
        simpa only [Real.norm_eq_abs,heₜ,mul_one] using (fderiv ℝ P z).le_opNorm (0,1)
      exact hh.trans (h₁ z hzU)
    have hJets := fixed_spatial_jet_bounds hPAt (h₁ z hzU) (h₂ z hzU)
    have hs := log_error_source_bound hm (hlow z hzQ) hA₀.le hb₀.le hR₀.le hP₁.le hP₂.le
      (hA z (hQK hzQ)) (hb z (hQK hzQ)) (hRF z (hQK hzQ)) htP hJets.1 hJets.2
    have hEquation := log_error_equation (F05CapOpen_isOpen k 2) hT hm
      (hab.1.mono ((hClosedQ.trans hQK).trans hKU)) hqCap hPCap
      (fun y hy => hlow y (hClosedQ hy))
      (F05_exp_equation_mono_space (F05_cap_radius_mono k (by norm_num)) heq) z hz
    have hEquationw : linearOp (cylinder (closure (F05CapOpen k 2)) 0 T) A β w z =
        (1-1/q z)*R z-timeD (cylinder (closure (F05CapOpen k 2)) 0 T) P z+
          (∑ i,∑ j,(a z i j/q z)*spatialDD P z (realVec i) (realVec j))+
          ∑ i,(b z i/q z)*spatialD P z (realVec i) := hEquation
    rw [F05_linearOp_cylinder_space_eq A β w hzQ.1 hzCap hzQ.2,hEquationw]
    exact hs.trans (by dsimp [H]; linarith)
  refine ⟨⟨hwc,hwreg.1,hwreg.2,hEllU,?_,?_,?_,?_,?_,hop⟩,?_⟩
  · intro z hz i j
    simpa only [Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      abs_div_bound hm (hlow z (hOpenQ hz)) hA₀.le (hA z (hQK (hOpenQ hz)) i j)
  · intro z hz i
    exact abs_div_bound hm (hlow z (hOpenQ hz)) hb₀.le (hb z (hQK (hOpenQ hz)) i)
  · intro x hx
    exact sub_eq_zero.mpr (hEqPoint (x,0) ⟨hx,le_rfl,hT.le⟩ (hi x hx)).symm
  · intro x hx t htm
    have hxRegion : x ∈ region k 2 := by
      have hxcl := frontier_subset_closure hx.1
      refine ⟨(show ‖x‖ < 2 by simpa only [Metric.mem_ball,dist_zero_right] using hx.2).le,?_⟩
      cases k <;> simpa only [F05FlatOpen_closure,mem_ofPred_eq] using hxcl
    exact sub_eq_zero.mpr (hEqPoint (x,t) ⟨hxRegion,htm⟩ (hl x hx t htm)).symm
  · intro z hz
    exact (log_error_value_bound hm (hbound z hz) (h₀ z (hQK hz))).trans
      (by dsimp [W₀]; linarith)
  · intro z hz
    exact exp_error_transfer hm (hbound z hz) (h₀ z (hQK hz))

end Yau.Proofs.F05Aux
