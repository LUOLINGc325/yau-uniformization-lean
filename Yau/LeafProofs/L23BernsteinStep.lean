import Yau.LeafProofs.L23BernsteinProduct

/-! The complete localized scalar step used in the curvature-jet induction. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def bernsteinScalarBound (σ B Dk Ek δ G L : ℝ) : ℝ :=
  let α := 1/(4*(17*B)^2)
  let β := (17*B*Dk+Ek)^2+17*B*Dk
  (2*(1+(L+σ*G)*δ)/(σ*α*δ)+Real.sqrt (2*β/α))/(16*B)

variable {n : ℕ} {M : ComplexManifold n}

theorem bernstein_local_scalar_step
    (h : ℝ → HermitianField M) (σ b T B Dk Ek G L : ℝ)
    (S : Set M.Carrier) (hS : IsCompact S) (hbT : b < T)
    (hσ : 0 < σ) (hB : 1 ≤ B) (hDk : 0 ≤ Dk) (hEk : 0 ≤ Ek)
    (hG : 0 ≤ G) (hL : 0 ≤ L)
    (v w z η : M.Carrier → ℝ → ℝ)
    (hv : ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (S ×ˢ Set.Icc b T))
    (hw : ContinuousOn (fun p : M.Carrier × ℝ => w p.1 p.2) (S ×ˢ Set.Icc b T))
    (hη : ContinuousOn (fun p : M.Carrier × ℝ => η p.1 p.2) (S ×ˢ Set.Icc b T))
    (hv0 : ∀ x ∈ S, ∀ t ∈ Set.Icc b T, 0 ≤ v x t)
    (hw0 : ∀ x ∈ S, ∀ t ∈ Set.Icc b T, 0 ≤ w x t)
    (hηRange : ∀ x ∈ S, ∀ t ∈ Set.Icc b T, 0 ≤ η x t ∧ η x t ≤ 1)
    (hηBoundary : ∀ x ∈ S, x ∉ interior S → ∀ t ∈ Set.Icc b T, η x t=0)
    (hvJoint : ∀ x ∈ interior S, ∀ t ∈ Set.Ioc b T,
      ContDiffAt ℝ 2 (fun p : ComplexVector n × ℝ => v (chartInv x p.1) p.2) (chartPt x x,t))
    (hwJoint : ∀ x ∈ interior S, ∀ t ∈ Set.Ioc b T,
      ContDiffAt ℝ 2 (fun p : ComplexVector n × ℝ => w (chartInv x p.1) p.2) (chartPt x x,t))
    (hSupports : ParabolicCutoffLowerSupports h σ η S b T G L)
    (hLocal : ∀ x ∈ interior S, ∀ t ∈ Set.Ioc b T, 0 < η x t →
      v x t ≤ B ∧ 0 ≤ z x t ∧
      flowOp h σ v x t ≤ -σ*w x t+σ*Ek ∧
      flowOp h σ w x t ≤ -σ*z x t+σ*Dk*(1+w x t) ∧
      realGradPair (h t) (fun y => v y t) (fun y => v y t) x ≤ 4*v x t*w x t ∧
      realGradPair (h t) (fun y => w y t) (fun y => w y t) x ≤ 4*w x t*z x t) :
    ∀ q ∈ S, η q T=1 → w q T ≤ bernsteinScalarBound σ B Dk Ek (T-b) G L := by
  intro q hq hqη
  let F := fun x t => (16*B+v x t)*w x t
  let α := 1/(4*(17*B)^2)
  let β := (17*B*Dk+Ek)^2+17*B*Dk
  have hBpos : 0 < B := by linarith
  have hα : 0 < α := by dsimp only [α]; positivity
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hF : ContinuousOn (fun p : M.Carrier × ℝ => F p.1 p.2) (S ×ˢ Set.Icc b T) :=
    (continuousOn_const.add hv).mul hw
  have hF0 (x : M.Carrier) (hx : x ∈ S) (t : ℝ) (ht : t ∈ Set.Icc b T) : 0 ≤ F x t := by
    exact mul_nonneg (add_nonneg (by positivity) (hv0 x hx t ht)) (hw0 x hx t ht)
  have hFjoint (x : M.Carrier) (hx : x ∈ interior S) (t : ℝ) (ht : t ∈ Set.Ioc b T) :
      ContDiffAt ℝ 2 (fun p : ComplexVector n × ℝ => F (chartInv x p.1) p.2) (chartPt x x,t) :=
    (contDiffAt_const.add (hvJoint x hx t ht)).mul (hwJoint x hx t ht)
  have hFop (x : M.Carrier) (hx : x ∈ interior S) (t : ℝ) (ht : t ∈ Set.Ioc b T)
      (hηpos : 0 < η x t) : flowOp h σ F x t ≤ -σ*α*(F x t)^2+σ*β := by
    obtain ⟨hvB,hz0,hvOp,hwOp,hvGrad,hwGrad⟩ := hLocal x hx t ht hηpos
    have hxS := interior_subset hx
    have htC : t ∈ Set.Icc b T := ⟨ht.1.le,ht.2⟩
    have hvJ := hvJoint x hx t ht
    have hwJ := hwJoint x hx t ht
    have hh := bernstein_product_evolution h σ B Dk Ek v w x t (z x t) hσ hB hDk hEk
      (hv0 x hxS t htC) hvB (hw0 x hxS t htC) hz0
      (distanceSupport_jointC2_space hvJ) (distanceSupport_jointC2_space hwJ)
      ((distanceSupport_jointC2_time hvJ).differentiableAt (by norm_num))
      ((distanceSupport_jointC2_time hwJ).differentiableAt (by norm_num)) hvOp hwOp hvGrad hwGrad
    convert hh using 1
    dsimp only [α,β,F]
    ring
  have hBound := nonlinear_cutoff_maximum h σ b T α β G L S hS hbT hσ hα hβ hG hL
    F η hF hη hF0 hηRange hηBoundary hFjoint hSupports hFop q hq hqη
  have hLower : 16*B*w q T ≤ F q T := by
    have hh := mul_nonneg (hv0 q hq T ⟨hbT.le,le_rfl⟩) (hw0 q hq T ⟨hbT.le,le_rfl⟩)
    dsimp only [F]
    nlinarith
  unfold bernsteinScalarBound
  apply (le_div_iff₀ (by positivity : 0 < 16*B)).mpr
  simpa only [α,β,mul_comm] using hLower.trans hBound

end Yau.LeafProofs.L23Aux
