import Yau.LeafProofs.L05ChuResidualCoarse
import Yau.LeafProofs.L16LocalizedClassicalEquation

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem tracePair_sym_eq_contraction {n : ℕ} (A : Sym n) (B : Mat n) :
    tracePair A (sym B)=∑ i, ∑ j, (A : Mat n) i j*B i j := by
  have hsym (i j : RIdx n) : (A : Mat n) j i=(A : Mat n) i j := by
    simpa only [star_trivial] using (Matrix.isHermitian_iff_isSelfAdjoint.mpr A.property).apply i j
  have hflip : (∑ i, ∑ j, (A : Mat n) i j*B j i)=(∑ i, ∑ j, (A : Mat n) i j*B i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym]
  unfold tracePair
  rw [sym_coe_formula]
  change (∑ i, ∑ j, (A : Mat n) i j*((1/2:ℝ)*(B j i+B i j)))=_
  calc
    _=(1/2:ℝ)*(∑ i, ∑ j, (A : Mat n) i j*B j i)+(1/2:ℝ)*(∑ i, ∑ j, (A : Mat n) i j*B i j) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _=_ := by rw [hflip]; ring

theorem chuFrozenLinear_eq_principal {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) (u : Point n → ℝ) (p : Point n) :
    chuFrozenLinear hT F A0 p0 hp0 (hessian u p)=
      ∑ i, ∑ j, (chuFrozenSlope hT F A0 p0 hp0 : Mat n) i j*
        spatialDD u p (Yau.realVec i) (Yau.realVec j) := by
  rw [chuFrozenLinear_trace]
  exact tracePair_sym_eq_contraction _ _

theorem chuFrozenResidual_eq_linearOp {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) {u : Point n → ℝ} (hu : C2 (backward 1) u)
    {O : Set (Space n)} {l r : ℝ} (hlr : l < r) (hQ : cylinder O l r ⊆ backward 1)
    {p : Point n} (hp : p ∈ cylinder O l r) :
    linearOp (cylinder O l r) (fun _ => (chuFrozenSlope hT F A0 p0 hp0 : Mat n)) (fun _ _ => 0) u p=
      chuFrozenResidual hT F A0 p0 hp0 u p := by
  simp only [linearOp,zero_mul,Finset.sum_const_zero,sub_zero,chuFrozenResidual,
    chu_timeD_cylinder_restrict_backward hlr hQ hu hp,chuFrozenLinear_eq_principal]

def chuFrozenCutoffSource {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) (phi : Space n → ℝ) (theta : ℝ → ℝ) (u : Point n → ℝ) (p : Point n) : ℝ :=
  theta p.2*(phi p.1*chuFrozenResidual hT F A0 p0 hp0 u p-
    L16Aux.spatialCutoffCommutator (fun _ => (chuFrozenSlope hT F A0 p0 hp0 : Mat n)) (fun _ _ => 0) phi u p)+
    deriv theta p.2*(phi p.1*u p)

theorem chu_frozen_cutoff_classical {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) {u : Point n → ℝ} (hu : C2 (backward 1) u)
    {O : Set (Space n)} (hO : IsOpen O) {l r : ℝ} (hlr : l < r)
    (hQ : cylinder O l r ⊆ backward 1) {phi : Space n → ℝ} (hphi : ContDiff ℝ 2 phi)
    (hSupport : tsupport phi ⊆ O) {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta) :
    C2 (cylinder Set.univ l r) (fun p => theta p.2*(phi p.1*u p)) ∧
      ∀ p ∈ cylinder Set.univ l r,
        linearOp (cylinder Set.univ l r) (fun _ => (chuFrozenSlope hT F A0 p0 hp0 : Mat n)) (fun _ _ => 0)
          (fun p => theta p.2*(phi p.1*u p)) p=chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u p := by
  exact L16Aux.localized_classical_cutoff_equation hlr hO hphi hSupport htheta
    (chu_c2_cylinder_restrict_backward hlr hQ hu)
    (fun _ => (chuFrozenSlope hT F A0 p0 hp0 : Mat n)) (fun _ _ => 0)
    (fun p hp => chuFrozenResidual_eq_linearOp hT F A0 p0 hp0 hu hlr hQ hp)

end Yau.LeafProofs.L05Aux
