import Yau.LeafProofs.L16ExpBoundaryBounds

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- The original nonlinear equation has a uniform initial modulus. The
transform and constant are chosen before q, and involve no derivative norm
of q or boundary ambient differentiability of the prescribed extension. -/
theorem actual_initial_modulus {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O)
    {T lam upper m B : ℝ} (hT : 0 < T) (hm : 0 < m) (hmB : m ≤ B)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {R p : Point n → ℝ}
    (hab : SmoothCoefficients (cylinder (closure O) 0 T) a b)
    (hR : ContDiffOn ℝ ∞ R (cylinder (closure O) 0 T))
    (hp : ContDiffOn ℝ ∞ p (cylinder (closure O) 0 T))
    (he : Elliptic (cylinder (closure O) 0 T) a lam upper) :
    ∃ (ℓ : ℝ → ℝ) (K : ℝ), 0 < K ∧ ContDiff ℝ ∞ ℓ ∧
      EqOn ℓ Real.log (Ioo (m/2) (B+1)) ∧
      ∀ q : Point n → ℝ, C2 (cylinder (closure O) 0 T) q →
        (∀ z ∈ cylinder (closure O) 0 T, m ≤ q z ∧ q z ≤ B) →
        DirichletData O T q p → ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R q →
        ∀ z ∈ cylinder (closure O) 0 T, |q z-Real.exp (ℓ (p z))| ≤ K*z.2 := by
  classical
  obtain ⟨ℓ,hℓ,hℓcompact,hℓeq,hP,P₀,P₁,P₂,hP₀,hP₁,hP₂,h₀,h₁,h₂⟩ :=
    fixed_log_data hO hm hmB hp
  obtain ⟨A₀,b₀,R₀,hA₀,hb₀,hR₀,hA,hb,hRF⟩ := compact_coefficient_source_bounds hO hab hR
  let H : ℝ := 1+(1+1/m)*R₀+P₁+
    (∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, (A₀/m)*P₂) +
      ∑ _i : Yau.RIdx n, (b₀/m)*P₁
  have hH : 0 < H := by dsimp [H]; positivity
  let E : ℝ := Real.exp (max (|Real.log m|+|Real.log B|) P₀)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨ℓ,E*H,mul_pos hE hH,hℓ,hℓeq,?_⟩
  intro q hq hbound hdata heq
  let P : Point n → ℝ := fun z => ℓ (p z)
  let w : Point n → ℝ := fun z => Real.log (q z)-P z
  let A : Point n → Mat n := fun z => (q z)⁻¹ • a z
  let β : Point n → Yau.RIdx n → ℝ := fun z j => b z j/q z
  have hlow : ∀ z ∈ cylinder (closure O) 0 T, m ≤ q z := fun z hz => (hbound z hz).1
  have hUK : O ×ˢ Ioo 0 T ⊆ cylinder (closure O) 0 T := by
    intro z hz
    exact ⟨subset_closure hz.1,Ioo_subset_Icc_self hz.2⟩
  have hwc : ContinuousOn w (cylinder (closure O) 0 T) :=
    log_error_continuous hm hq.1 hP.continuousOn hlow
  have hwreg := log_error_interior_regularity hO.1 hm hq hP hlow
  have hwdata : DirichletData O T w (fun _ => 0) :=
    (fixed_log_boundary_agreement hT.le hm hℓeq hbound hdata).2
  have hEll := L16Aux.elliptic_div_of_bounds he hm hmB hbound
  have hEllU : Elliptic (O ×ˢ Ioo 0 T) A (lam/B) (upper/m) :=
    ⟨hEll.1,hEll.2.1,fun z hz => hEll.2.2 z (hUK hz)⟩
  have hop : ∀ z ∈ O ×ˢ Ioo 0 T,
      |linearOp (cylinder (closure O) 0 T) A β w z| ≤ H := by
    intro z hz
    have hPAt : ContDiffAt ℝ 2 P z :=
      ((hP.mono hUK).contDiffAt ((hO.1.prod isOpen_Ioo).mem_nhds hz)).of_le (by simp)
    have hPtime : DifferentiableAt ℝ (fun t => P (z.1,t)) z.2 :=
      DifferentiableAt.comp (g := P) (f := fun t : ℝ => (z.1,t)) z.2
        (hPAt.differentiableAt (by norm_num))
        ((differentiableAt_const z.1).prodMk differentiableAt_id)
    have htP : |timeD (cylinder (closure O) 0 T) P z| ≤ P₁ := by
      rw [timeD_closed_eq_deriv hT (hUK hz).1 (hUK hz).2 hPtime,
        L16Aux.test_timeDerivative_eq_joint_fderiv (φ := P) (hPAt.differentiableAt (by norm_num))]
      have heₜ : ‖((0 : Space n),(1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
      have hh : |fderiv ℝ P z (0,1)| ≤ ‖fderiv ℝ P z‖ := by
        simpa only [Real.norm_eq_abs,heₜ,mul_one] using (fderiv ℝ P z).le_opNorm (0,1)
      exact hh.trans (h₁ z hz)
    have hJets := fixed_spatial_jet_bounds hPAt (h₁ z hz) (h₂ z hz)
    have hs := log_error_source_bound hm (hlow z (hUK hz)) hA₀.le hb₀.le hR₀.le hP₁.le hP₂.le
      (hA z (hUK hz)) (hb z (hUK hz)) (hRF z (hUK hz)) htP hJets.1 hJets.2
    change |linearOp (cylinder (closure O) 0 T) (fun z => (q z)⁻¹ • a z)
      (fun z j => b z j/q z) (fun z => Real.log (q z)-P z) z| ≤ H
    rw [log_error_equation hO.1 hT hm hab.1 hq hP hlow heq z hz]
    exact hs.trans (by dsimp [H]; linarith)
  have hwInitial := initial_barrier_abs_openTop (b := β) hO.1 hO.2.2.1 hT hH.le
    hwc hwreg.1 hwreg.2 hEllU hwdata.1 hwdata.2 hop
  intro z hz
  have hh := exp_error_transfer hm (hbound z hz) (h₀ z hz)
  have hh' : |q z-Real.exp (ℓ (p z))| ≤ E*|w z| := hh
  exact hh'.trans ((mul_le_mul_of_nonneg_left (hwInitial z hz) hE.le).trans_eq (by ring))

end Yau.LeafProofs.L16ExpBoundaryAux
