import Yau.LeafProofs.L05AutonomousDirections

noncomputable section
open scoped Topology Matrix Matrix.Norms.Frobenius
open Finset Matrix
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

local instance autoLocalFrameSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

local instance autoLocalFrame_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoLocalFrame_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance autoLocalFrame_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance autoLocalFrame_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The symmetric matrix acts as its actual real continuous bilinear form. -/
def autoBilinearMap (n : ℕ) : Sym n →L[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ∑ i, ∑ j, (symEntry n i j).smulRight
    ((innerSL ℝ (Yau.realVec i)).smulRight (innerSL ℝ (Yau.realVec j)))

theorem autoBilinearMap_apply {n : ℕ} (H : Sym n) (v w : Space n) :
    autoBilinearMap n H v w =
      ∑ i, ∑ j, (H : Mat n) i j*inner ℝ (Yau.realVec i) v*inner ℝ (Yau.realVec j) w := by
  simp only [autoBilinearMap,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    innerSL_apply_apply,symEntry]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (H : Mat n) i j*(inner ℝ (Yau.realVec i) v*inner ℝ (Yau.realVec j) w)=_
  ring

theorem autoBilinearMap_symmetric {n : ℕ} (H : Sym n) (v w : Space n) :
    autoBilinearMap n H v w=autoBilinearMap n H w v := by
  have hs (i j) : (H : Mat n) i j=(H : Mat n) j i := by
    simpa only [star_trivial] using
      (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.property).apply j i
  rw [autoBilinearMap_apply,autoBilinearMap_apply,Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hs i j]; ring

theorem autoBilinearMap_realVec {n : ℕ} (H : Sym n) (i j : Yau.RIdx n) :
    autoBilinearMap n H (Yau.realVec i) (Yau.realVec j)=(H : Mat n) i j := by
  rw [autoBilinearMap_apply]
  simp [auto_realVec_inner]

def autoBasisMatrix {n : ℕ} (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n))
    (H : Sym n) : Mat n := fun i j => autoBilinearMap n H (b i) (b j)

theorem autoBasisMatrix_symmetric {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (H : Sym n) (i j) :
    autoBasisMatrix b H i j=autoBasisMatrix b H j i :=
  autoBilinearMap_symmetric H _ _

theorem autoBasisMatrix_continuous {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (i j : Yau.RIdx n) :
    Continuous (fun H : Sym n => autoBasisMatrix b H i j) :=
  (((autoBilinearMap n).continuous.clm_apply continuous_const).clm_apply continuous_const)

theorem autoBasisMatrix_reconstruction {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (H : Sym n) (k l : Yau.RIdx n) :
    (H : Mat n) k l =
      ∑ i, ∑ j, autoBasisMatrix b H i j*
        inner ℝ (Yau.realVec k) (b i)*inner ℝ (Yau.realVec l) (b j) := by
  calc
    _ = autoBilinearMap n H (∑ i, inner ℝ (b i) (Yau.realVec k) • b i)
        (∑ j, inner ℝ (b j) (Yau.realVec l) • b j) := by
      rw [b.sum_repr',b.sum_repr',autoBilinearMap_realVec]
    _ = _ := by
      simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply,smul_eq_mul,autoBasisMatrix,real_inner_comm,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Repeated directions are retained, so the indexing needs no arbitrary ordering. -/
abbrev AutoLocalIndex (n : ℕ) := Yau.RIdx n ⊕ (Yau.RIdx n × Yau.RIdx n × Fin 2)

def autoLocalDirection {n : ℕ} (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) :
    AutoLocalIndex n → Space n
  | Sum.inl i => b i
  | Sum.inr (i,j,s) => if i=j then b i else
      (Real.sqrt 2)⁻¹ • (b i+(if s=0 then (1:ℝ) else -1) • b j)

def autoLocalCoefficient {n : ℕ} (a0 : ℝ) (C : Mat n) : AutoLocalIndex n → ℝ
  | Sum.inl i => C i i-(2*n:ℝ)*a0
  | Sum.inr (i,j,s) => if i=j then a0/2 else
      (a0+(if s=0 then (1:ℝ) else -1)*C i j)/2

theorem autoLocalDirection_norm {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (k : AutoLocalIndex n) :
    ‖autoLocalDirection b k‖=1 := by
  rcases k with i | ⟨i,j,s⟩
  · exact b.norm_eq_one i
  by_cases hij : i=j
  · simp only [autoLocalDirection, if_pos hij, b.norm_eq_one]
  have hs (c : ℝ) (hc : c^2=1) : ‖b i+c • b j‖=Real.sqrt 2 := by
    have hsq : ‖b i+c • b j‖^2=2 := by
      rw [norm_add_sq_real, b.norm_eq_one, norm_smul, Real.norm_eq_abs,
        b.norm_eq_one, mul_one, inner_smul_right, b.inner_eq_zero hij]
      nlinarith only [hc,sq_abs c]
    nlinarith only [hsq,norm_nonneg (b i+c • b j),
      Real.sqrt_nonneg (2:ℝ),Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simp only [autoLocalDirection, ite_eq_right hij, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [hs _ (by split_ifs <;> norm_num),inv_mul_cancel₀ (by positivity)]

/-- Each signed pair has the literal positive diagonal mass and off-diagonal coefficient. -/
theorem autoLocal_pair_entry {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (a0 : ℝ) (C : Mat n)
    (i j k l : Yau.RIdx n) :
    (∑ s : Fin 2, autoLocalCoefficient a0 C (.inr (i,j,s)) *
      (autoRankOne (autoLocalDirection b (.inr (i,j,s))) : Mat n) k l) =
    a0/2*(inner ℝ (Yau.realVec k) (b i)*inner ℝ (Yau.realVec l) (b i)+
      inner ℝ (Yau.realVec k) (b j)*inner ℝ (Yau.realVec l) (b j)) +
    C i j/2*(inner ℝ (Yau.realVec k) (b i)*inner ℝ (Yau.realVec l) (b j)+
      inner ℝ (Yau.realVec k) (b j)*inner ℝ (Yau.realVec l) (b i)) -
    (if i=j then C i i*inner ℝ (Yau.realVec k) (b i)*inner ℝ (Yau.realVec l) (b i)
      else 0) := by
  rw [Fin.sum_univ_two]
  simp only [autoLocalCoefficient, autoLocalDirection, Fin.reduceEq, ite_true,
    ite_false, autoRankOne_coe]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    ring
  simp only [ite_eq_right hij, inner_smul_right, inner_add_right,
    one_smul, neg_one_smul, inner_neg_right]
  have hsqrt : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2≠0 := by positivity
  field_simp
  rw [hsqrt]
  ring

theorem auto_symmetric_pair_sum {n : ℕ} (C : Mat n)
    (hC : ∀ i j, C i j=C j i) (x y : Yau.RIdx n → ℝ) :
    (∑ i, ∑ j, C i j/2*(x i*y j+x j*y i)) = ∑ i, ∑ j, C i j*x i*y j := by
  have hswap : (∑ i, ∑ j, C i j*x j*y i)=(∑ i, ∑ j, C i j*x i*y j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hC j i]
  calc
    _ = (∑ i, ∑ j, C i j*x i*y j)/2+(∑ i, ∑ j, C i j*x j*y i)/2 := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_div]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
        apply Finset.sum_congr rfl <;> intro j _ <;> ring
    _ = _ := by rw [hswap]; ring

/-- The local frame represents a matrix by genuine scalar rank-one coefficients. -/
theorem autoLocal_representation {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (a0 : ℝ) (C : Mat n)
    (hC : ∀ i j, C i j=C j i) (H : Sym n)
    (hrep : ∀ k l, (H : Mat n) k l =
      ∑ i, ∑ j, C i j*inner ℝ (Yau.realVec k) (b i)*inner ℝ (Yau.realVec l) (b j)) :
    H=∑ q, autoLocalCoefficient a0 C q • autoRankOne (autoLocalDirection b q) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  ext k l
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  change (H : Mat n) k l = ∑ q : AutoLocalIndex n,
    autoLocalCoefficient a0 C q*(autoRankOne (autoLocalDirection b q) : Mat n) k l
  rw [Fintype.sum_sum_type]
  have hdiag_entry (i : Yau.RIdx n) :
      autoLocalCoefficient a0 C (.inl i)*(autoRankOne (autoLocalDirection b (.inl i)) : Mat n) k l =
      (C i i-(2*n:ℝ)*a0)*inner ℝ (Yau.realVec k) (b i)*inner ℝ (Yau.realVec l) (b i) := by
    rw [autoRankOne_coe]
    dsimp only [autoLocalCoefficient,autoLocalDirection]
    ring
  simp only [hdiag_entry]
  change (H : Mat n) k l =
    (∑ i, (C i i-(2*n:ℝ)*a0)*inner ℝ (Yau.realVec k) (b i)*inner ℝ (Yau.realVec l) (b i)) +
    ∑ p : Yau.RIdx n × Yau.RIdx n × Fin 2,
      autoLocalCoefficient a0 C (.inr p)*(autoRankOne (autoLocalDirection b (.inr p)) : Mat n) k l
  have hsplit : (∑ p : Yau.RIdx n × Yau.RIdx n × Fin 2,
      autoLocalCoefficient a0 C (.inr p)*(autoRankOne (autoLocalDirection b (.inr p)) : Mat n) k l) =
      ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, ∑ s : Fin 2,
        autoLocalCoefficient a0 C (.inr (i,j,s))*
          (autoRankOne (autoLocalDirection b (.inr (i,j,s))) : Mat n) k l := by
    simp only [Fintype.sum_prod_type]
  rw [hsplit]
  simp only [autoLocal_pair_entry]
  let x : Yau.RIdx n → ℝ := fun i => inner ℝ (Yau.realVec k) (b i)
  let y : Yau.RIdx n → ℝ := fun i => inner ℝ (Yau.realVec l) (b i)
  change (H : Mat n) k l = (∑ i, (C i i-(2*n:ℝ)*a0)*x i*y i)+
    ∑ i, ∑ j, (a0/2*(x i*y i+x j*y j)+C i j/2*(x i*y j+x j*y i)-
      if i=j then C i i*x i*y i else 0)
  have hcard : (Fintype.card (Yau.RIdx n):ℝ)=2*n := by simp [Yau.RIdx]; ring
  have hbase : (∑ i, ∑ j, a0/2*(x i*y i+x j*y j))=
      (2*n:ℝ)*a0*(∑ i, x i*y i) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,← Finset.mul_sum,← Finset.sum_mul,hcard]
    ring
  have hdiag : (∑ i, (C i i-(2*n:ℝ)*a0)*x i*y i)=
      (∑ i, C i i*x i*y i)-(2*n:ℝ)*a0*(∑ i, x i*y i) := by
    simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  rw [hdiag]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [hbase,auto_symmetric_pair_sum C hC]
  rw [hrep k l]
  dsimp only [x,y]
  ring

theorem autoLocal_actual_representation {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (a0 : ℝ) (H : Sym n) :
    H=∑ q, autoLocalCoefficient a0 (autoBasisMatrix b H) q •
      autoRankOne (autoLocalDirection b q) :=
  autoLocal_representation b a0 _ (autoBasisMatrix_symmetric b H) H
    (autoBasisMatrix_reconstruction b H)

theorem autoLocalCoefficient_continuous {n : ℕ}
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (a0 : ℝ) (q : AutoLocalIndex n) :
    Continuous (fun H : Sym n => autoLocalCoefficient a0 (autoBasisMatrix b H) q) := by
  rcases q with i | ⟨i,j,s⟩
  · exact (autoBasisMatrix_continuous b i i).sub continuous_const
  by_cases hij : i=j
  · simpa only [autoLocalCoefficient,ite_eq_left hij] using
      (continuous_const : Continuous (fun _ : Sym n => a0/2))
  simpa only [autoLocalCoefficient,ite_eq_right hij,Pi.add_apply,Pi.mul_apply] using
    (continuous_const.add (continuous_const.mul (autoBasisMatrix_continuous b i j))).div_const 2

/-- The explicit coefficients stay positive on a genuine open neighborhood of a diagonal center. -/
theorem autoLocal_positive_neighborhood {n : ℕ} (hn : 0<n) {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L)
    (b : OrthonormalBasis (Yau.RIdx n) ℝ (Space n)) (B : Sym n)
    (hdiag : ∀ i, (ell/2)≤autoBasisMatrix b B i i ∧ autoBasisMatrix b B i i≤L)
    (hoff : ∀ i j, i≠j → autoBasisMatrix b B i j=0) :
    ∃ U : Set (Sym n), IsOpen U ∧ B∈U ∧
      ∀ H∈U, ∀ q, autoLocalCoefficient (ell/(8*(2*n))) (autoBasisMatrix b H) q∈Set.Ioo 0 (2*L) := by
  let a0 : ℝ := ell/(8*(2*n))
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have ha : 0<a0 := by dsimp only [a0]; positivity
  have hda : (2*n:ℝ)*a0=ell/8 := by dsimp only [a0]; field_simp
  have haL : a0<L := by
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
    nlinarith only [hda,ha,hn1,hL,hell]
  let U : Set (Sym n) := {H | ∀ q, autoLocalCoefficient a0 (autoBasisMatrix b H) q∈Set.Ioo 0 (2*L)}
  refine ⟨U,?_,?_,fun _ hH => hH⟩
  · change IsOpen {H : Sym n | ∀ q, autoLocalCoefficient a0 (autoBasisMatrix b H) q∈Set.Ioo 0 (2*L)}
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun q => isOpen_Ioo.preimage (autoLocalCoefficient_continuous b a0 q)
  intro q
  rcases q with i | ⟨i,j,s⟩
  · change 0<autoBasisMatrix b B i i-(2*n:ℝ)*a0 ∧
      autoBasisMatrix b B i i-(2*n:ℝ)*a0<2*L
    rw [hda]
    constructor <;> linarith only [(hdiag i).1,(hdiag i).2,hell,hL]
  by_cases hij : i=j
  · simp only [autoLocalCoefficient,ite_eq_left hij,Set.mem_Ioo]
    constructor <;> linarith only [ha,haL,hell,hL]
  simp only [autoLocalCoefficient,ite_eq_right hij,hoff i j hij,mul_zero,add_zero,Set.mem_Ioo]
  constructor <;> linarith only [ha,haL,hell,hL]

theorem auto_real_coordinates_repr_symm {n : ℕ}
    (v : EuclideanSpace ℝ (Yau.RIdx n)) (i : Yau.RIdx n) :
    inner ℝ (Yau.realVec i) ((complexVector_realOrthonormalBasis n).repr.symm v)=v i := by
  have hh := congrArg (fun w : EuclideanSpace ℝ (Yau.RIdx n) => w i)
    ((complexVector_realOrthonormalBasis n).repr.apply_symm_apply v)
  simpa only [OrthonormalBasis.repr_apply_apply,complexVector_realOrthonormalBasis_apply] using hh

def autoEigenBasis {n : ℕ} (B : Sym n) : OrthonormalBasis (Yau.RIdx n) ℝ (Space n) :=
  (Matrix.isHermitian_iff_isSelfAdjoint.mpr B.property).eigenvectorBasis.map
    (complexVector_realOrthonormalBasis n).repr.symm

theorem autoEigenBasis_diagonal {n : ℕ} (B : Sym n) (i j : Yau.RIdx n) :
    autoBasisMatrix (autoEigenBasis B) B i j =
      if i=j then (Matrix.isHermitian_iff_isSelfAdjoint.mpr B.property).eigenvalues i else 0 := by
  let hB : (B : Mat n).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr B.property
  have heq : autoBasisMatrix (autoEigenBasis B) B i j =
      star (hB.eigenvectorBasis i).ofLp ⬝ᵥ ((B : Mat n) *ᵥ (hB.eigenvectorBasis j).ofLp) := by
    rw [autoBasisMatrix,autoBilinearMap_apply]
    simp only [autoEigenBasis,OrthonormalBasis.map_apply,auto_real_coordinates_repr_symm,
      dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  change autoBasisMatrix (autoEigenBasis B) B i j = if i=j then hB.eigenvalues i else 0
  rw [heq,hB.mulVec_eigenvectorBasis,dotProduct_smul]
  rw [dotProduct_comm,← EuclideanSpace.inner_eq_star_dotProduct,(hB.eigenvectorBasis).inner_eq_ite]
  by_cases hij : i=j
  · subst j
    simp [hB]
  simp [hij]

theorem autoEigenBasis_slope_diagonal_bounds {n : ℕ} {ell L : ℝ}
    (B : Sym n) (hB : B∈slopeSet n ell L) (i : Yau.RIdx n) :
    ell≤autoBasisMatrix (autoEigenBasis B) B i i ∧
      autoBasisMatrix (autoEigenBasis B) B i i≤L := by
  let hHerm : (B : Mat n).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr B.property
  let v := (hHerm.eigenvectorBasis i).ofLp
  have hv : star v ⬝ᵥ v=1 := by
    change star (hHerm.eigenvectorBasis i).ofLp ⬝ᵥ (hHerm.eigenvectorBasis i).ofLp=1
    rw [dotProduct_comm,← EuclideanSpace.inner_eq_star_dotProduct]
    exact (hHerm.eigenvectorBasis).inner_eq_one i
  have heig : star v ⬝ᵥ ((B : Mat n) *ᵥ v)=hHerm.eigenvalues i := by
    dsimp only [v]
    rw [hHerm.mulVec_eigenvectorBasis,dotProduct_smul]
    change (hHerm.eigenvalues i) • (star v ⬝ᵥ v)=_
    rw [hv,smul_eq_mul,mul_one]
  have hl := hB.1.dotProduct_mulVec_nonneg v
  have hu := hB.2.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,heig,hv,smul_eq_mul,mul_one] at hl
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,heig,hv,smul_eq_mul,mul_one] at hu
  rw [autoEigenBasis_diagonal,ite_eq_left rfl]
  change ell≤hHerm.eigenvalues i ∧ hHerm.eigenvalues i≤L
  exact ⟨sub_nonneg.mp hl,sub_nonneg.mp hu⟩

end Yau.LeafProofs.L05AutonomousAux
