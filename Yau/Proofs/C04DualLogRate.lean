import Yau.Proofs.C04MatrixProductDerivative
import Yau.Proofs.C04MatrixHarnackForms

/-! Matrix Harnack gives convexity of each genuine dual logarithmic norm in logarithmic time. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def dualValue (h : ℝ → HermitianField M) (x : M.Carrier) (v : Fin n → ℂ) (t : ℝ) : ℝ :=
  Blueprint.Alignment.Y03Proof.matrixForm (gMat (h t) x)⁻¹ v

def dualNumerator (h : ℝ → HermitianField M) (x : M.Carrier) (v : Fin n → ℂ) (t : ℝ) : ℝ :=
  let K := (gMat (h t) x)⁻¹
  Blueprint.Alignment.Y03Proof.matrixForm (K * ricci (h t) x * K) v

def dualClockRate (h : ℝ → HermitianField M) (x : M.Carrier) (v : Fin n → ℂ) (t : ℝ) : ℝ :=
  t * dualNumerator h x v t / dualValue h x v t

def dualLog (h : ℝ → HermitianField M) (x : M.Carrier) (v : Fin n → ℂ) (t : ℝ) : ℝ :=
  Real.log (dualValue h x v t)

theorem dualValue_pos (h : ℝ → HermitianField M) (x : M.Carrier)
    (v : Fin n → ℂ) (hv : v ≠ 0) (t : ℝ) : 0 < dualValue h x v t :=
  (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)).inv.re_dotProduct_pos hv

theorem dualValue_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (v : Fin n → ℂ) :
    HasDerivAt (dualValue h x v) (dualNumerator h x v t) t :=
  inverse_form_hasDerivAt X o h U P ρ hf x ht v

theorem dualClockRate_nonneg (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (hH : HarnackCompleteness X o h) (x : Pt X)
    {t : ℝ} (ht : 0 < t) (v : Fin n → ℂ) (hv : v ≠ 0) :
    0 ≤ dualClockRate h x v t := by
  have hK : ((gMat (h t) x)⁻¹).IsHermitian :=
    (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)).inv.isHermitian
  have hN := (hH.2.2.1 t ht.le x).posSemidef.conjTranspose_mul_mul_same (gMat (h t) x)⁻¹
  rw [hK.eq] at hN
  exact div_nonneg (mul_nonneg ht.le (hN.re_dotProduct_nonneg v)) (dualValue_pos h x v hv t).le

theorem dualNumerator_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (v : Fin n → ℂ) :
    let K := (gMat (h t) x)⁻¹
    let R := ricci (h t) x
    let R' := Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t)
    HasDerivAt (dualNumerator h x v)
      (Blueprint.Alignment.Y03Proof.matrixForm (K * R' * K) v +
        2 * Blueprint.Alignment.Y03Proof.matrixForm (K * R * K * R * K) v) t := by
  dsimp only [dualNumerator]
  change HasDerivAt (fun s => Blueprint.Alignment.Y03Proof.matrixForm
    ((gMat (h s) x)⁻¹ * ricci (h s) x * (gMat (h s) x)⁻¹) v) _ t
  have hh := Blueprint.Alignment.Y03Proof.matrixForm_hasDerivAt _ _
    (inverse_ricci_inverse_hasDerivAt X o h U P ρ hf x ht) v
  simpa only [dualNumerator, matrixForm_add, two_mul, add_assoc] using hh

theorem dualClockRate_differentiableAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (v : Fin n → ℂ) (hv : v ≠ 0) :
    DifferentiableAt ℝ (dualClockRate h x v) t :=
  (differentiableAt_id.mul (dualNumerator_hasDerivAt X o h U P ρ hf x ht v).differentiableAt).div
    (dualValue_hasDerivAt X o h U P ρ hf x ht v).differentiableAt (dualValue_pos h x v hv t).ne'

theorem dualClockRate_deriv_nonneg (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (v : Fin n → ℂ) (hv : v ≠ 0) : 0 ≤ deriv (dualClockRate h x v) t := by
  let K := (gMat (h t) x)⁻¹
  let R := ricci (h t) x
  let R' := Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t)
  let F := dualValue h x v t
  let N := dualNumerator h x v t
  let T := Blueprint.Alignment.Y03Proof.matrixForm (K * R' * K) v
  let V := Blueprint.Alignment.Y03Proof.matrixForm (K * R * K * R * K) v
  have hF : 0 < F := dualValue_pos h x v hv t
  have hdF := dualValue_hasDerivAt X o h U P ρ hf x ht v
  have hdN := dualNumerator_hasDerivAt X o h U P ρ hf x ht v
  have hd := ((hasDerivAt_id t).mul hdN).div hdF hF.ne'
  have hformula : deriv (dualClockRate h x v) t =
      N / F + t * (((T + 2 * V) * F - N ^ 2) / F ^ 2) := by
    change deriv (id * dualNumerator h x v / dualValue h x v) t = _
    rw [hd.deriv]
    change ((1 * N + t * (T + 2 * V)) * F - (t * N) * N) / F ^ 2 = _
    field_simp [hF.ne'] <;> ring
  rw [hformula]
  have hK : K.PosDef :=
    (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)).inv
  have hR : R.IsHermitian := (hH.2.2.1 t ht.le x).isHermitian
  exact matrix_harnack_lograte_nonneg K R R' hK hR t ht (hH.2.2.2.1 x t ht) v hv

theorem dualClockRate_monotoneOn (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (x : Pt X) (v : Fin n → ℂ) (hv : v ≠ 0)
    {A : ℝ} (hA : 0 < A) : MonotoneOn (dualClockRate h x v) (Set.Ici A) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici A)
  · intro t ht
    exact (dualClockRate_differentiableAt X o h U P ρ hf x (hA.trans_le ht) v hv).continuousAt.continuousWithinAt
  · intro t ht
    exact (dualClockRate_differentiableAt X o h U P ρ hf x (hA.trans_le (interior_subset ht)) v hv).differentiableWithinAt
  · intro t ht
    exact dualClockRate_deriv_nonneg X o h U P ρ hf hH x (hA.trans_le (interior_subset ht)) v hv

theorem dualLog_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (v : Fin n → ℂ) (hv : v ≠ 0) :
    HasDerivAt (dualLog h x v) (dualClockRate h x v t / t) t := by
  have hh := (dualValue_hasDerivAt X o h U P ρ hf x ht v).log (dualValue_pos h x v hv t).ne'
  have heq : dualClockRate h x v t / t = dualNumerator h x v t / dualValue h x v t := by
    unfold dualClockRate
    field_simp [ht.ne', (dualValue_pos h x v hv t).ne']
  rw [heq]
  exact hh

theorem dualLog_secant (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (x : Pt X) (v : Fin n → ℂ) (hv : v ≠ 0)
    {u t : ℝ} (hu : 0 < u) (hut : u ≤ t) :
    dualLog h x v t - dualLog h x v u ≤
      dualClockRate h x v t * (Real.log t - Real.log u) :=
  logarithmic_secant hu
    (fun s hs => dualLog_hasDerivAt X o h U P ρ hf x (hu.trans_le hs) v hv)
    (dualClockRate_monotoneOn X o h U P ρ hf hH x v hv hu) (le_refl u) hut

end Yau.Proofs.C04Aux
