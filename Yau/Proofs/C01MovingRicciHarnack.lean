import Yau.Proofs.C01MovingQuadraticJets

/-! The original matrix differential Harnack inequality is the derivative
of t times Ricci evaluated on an actual moving frame. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

def movingFrameMatrix (h : Flow X) (x : Pt X) (t : ℝ) : Herm n :=
  (1 / 2 : ℂ) • ((gMat (h t) x)⁻¹ * ricci (h t) x)

theorem localizedFlow_moving_ricci_weight_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (v : ℝ → Fin n → ℂ) {t : ℝ} (ht : 0 < t)
    (hframe : ∀ i, HasDerivAt (fun s => v s i) ((movingFrameMatrix h x t *ᵥ v t) i) t) :
    HasDerivAt (fun s => s * (star (v s) ⬝ᵥ (ricci (h s) x *ᵥ v s)).re)
      (t * (star (v t) ⬝ᵥ ((Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t) +
        ricci (h t) x * (gMat (h t) x)⁻¹ * ricci (h t) x +
        ((t⁻¹ : ℝ) : ℂ) • ricci (h t) x) *ᵥ v t)).re) t := by
  let H := gMat (h t) x
  let A := ricci (h t) x
  let D := Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t)
  let M := movingFrameMatrix h x t
  let B : Herm n := Mᴴ * A + D + A * M
  let Q : Herm n := D + A * H⁻¹ * A + ((t⁻¹ : ℝ) : ℂ) • A
  have hH : H.IsHermitian := (Alignment.Y03Proof.hMat_posDef (h t) x
    (chartPt x x) (mem_extChartAt_target (I := ComplexModel n) x)).isHermitian
  have hA : A.IsHermitian := localizedFlow_ricci_isHermitian hflow x ht
  have hfactor : A + (t : ℂ) • B = (t : ℂ) • Q := by
    have horder : Mᴴ * A + D + A * M = D + (Mᴴ * A + A * M) := by abel
    change A + (t : ℂ) • (Mᴴ * A + D + A * M) = _
    rw [horder, add_comm]
    exact moving_frame_harnack_factor H A D hH hA ht
  have hd := matrix_moving_quadratic_hasDerivAt (fun s => ricci (h s) x) v D M t
    (fun i j => localizedFlow_ricci_hasDerivAt hflow x ht i j) hframe
  have hreal : HasDerivAt (fun s => (star (v s) ⬝ᵥ (ricci (h s) x *ᵥ v s)).re)
      (star (v t) ⬝ᵥ (B *ᵥ v t)).re t := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.reCLM_apply] using!
        (Complex.reCLM.hasFDerivAt.comp t hd.hasFDerivAt).hasDerivAt
  have hquad := congrArg (fun C : Herm n => (star (v t) ⬝ᵥ (C *ᵥ v t)).re) hfactor
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_re, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hquad
  change HasDerivAt _ (t * (star (v t) ⬝ᵥ (Q *ᵥ v t)).re) t
  convert! (hasDerivAt_id t).mul hreal using 1
  simpa only [one_mul, id_eq, A] using hquad.symm

theorem localizedFlow_moving_ricci_weight_monotoneOn
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) (x : Pt X)
    (v : ℝ → Fin n → ℂ) (a b : ℝ) (ha : 0 < a)
    (hframe : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun s => v s i) ((movingFrameMatrix h x t *ᵥ v t) i) t) :
    MonotoneOn (fun t => t * (star (v t) ⬝ᵥ (ricci (h t) x *ᵥ v t)).re) (Set.Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    localizedFlow_moving_ricci_weight_hasDerivAt hflow x v (ha.trans_le ht.1) (hframe t ht)
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have htc := interior_subset ht
    rw [(hd t htc).deriv]
    exact mul_nonneg (ha.trans_le htc.1).le
      (Complex.nonneg_iff.mp
        ((localizedFlow_matrix_harnack hflow hjoint x (ha.trans_le htc.1)).dotProduct_mulVec_nonneg
          (v t))).1

end Yau.NodeProofs.C01Aux
