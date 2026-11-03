import Yau.LeafProofs.L05BellmanExtension
import Yau.LeafProofs.L05TransformNorm

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuGlobalOperator {n : ℕ} (E : Set (Sym n)) (F : Sym n → Point n → ℝ)
    (S : Point n → Sym n) (T : Sym n → Point n → Sym n) (ell L : ℝ) (H : Sym n) (p : Point n) : ℝ :=
  bellmanExtension E F ell L (S p+T H p) p

def bellmanMatrixConstant (n : ℕ) (L : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (RIdx n))*((2*n)*L)

theorem bellmanMatrixConstant_nonneg (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ bellmanMatrixConstant n L := by unfold bellmanMatrixConstant; positivity

theorem chuGlobalOperator_eq_on {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hEv : Convex ℝ E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hF : ChuH1 E U F ell L K beta)
    {H : Sym n} {p : Point n} (hp : p ∈ backward 1) (hH : S p+T H p ∈ E) :
    chuGlobalOperator E F S T ell L H p=F (S p+T H p) p :=
  bellmanExtension_eq_on hEc hEv hne hell hL hF hH hp

theorem chuGlobalOperator_globalElliptic {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hF : ChuH1 E U F ell L K beta)
    (hT : ChuH2 T K beta) {p : Point n} (hp : p ∈ backward 1) :
    globalElliptic (fun H => chuGlobalOperator E F S T ell L H p)
      (ell*K⁻¹) (Real.sqrt (Fintype.card (RIdx n))*K*L) := by
  intro N P hP
  have hTP := (hT.2.2.2 P hP p hp).1
  have he := bellmanExtension_globalElliptic hEc hne hell hL (chu_matrix_continuousOn hF hp)
    (S p+T N p) (T P p) hTP
  have ht := chuTransform_trace_bounds hT hp hP
  have hl := mul_le_mul_of_nonneg_left ht.1 hell
  have hu := mul_le_mul_of_nonneg_left ht.2 (hell.trans hL)
  have hadd : S p+T (N+P) p=(S p+T N p)+T P p := by rw [hT.2.1 p hp]; abel
  change (ell*K⁻¹)*Matrix.trace (P : Mat n) ≤
    bellmanExtension E F ell L (S p+T (N+P) p) p-bellmanExtension E F ell L (S p+T N p) p ∧
    bellmanExtension E F ell L (S p+T (N+P) p) p-bellmanExtension E F ell L (S p+T N p) p ≤
      (Real.sqrt (Fintype.card (RIdx n))*K*L)*Matrix.trace (P : Mat n)
  rw [hadd]
  constructor <;> nlinarith only [he.1,he.2,hl,hu]

theorem chuGlobalOperator_concave {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hF : ChuH1 E U F ell L K beta)
    (hT : ChuH2 T K beta) {p : Point n} (hp : p ∈ backward 1) :
    ConcaveOn ℝ Set.univ (fun H => chuGlobalOperator E F S T ell L H p) := by
  refine ⟨convex_univ,?_⟩
  intro N hN M hM a b ha hb hab
  have hh := (bellmanExtension_concave hEc hne hell hL (chu_matrix_continuousOn hF hp)).2
    (show S p+T N p ∈ Set.univ from Set.mem_univ _) (show S p+T M p ∈ Set.univ from Set.mem_univ _) ha hb hab
  have hS : a • S p+b • S p=S p := by rw [← add_smul,hab,one_smul]
  have harg : S p+T (a • N+b • M) p=a • (S p+T N p)+b • (S p+T M p) := by
    rw [hT.2.1 p hp,hT.2.2.1 p hp,hT.2.2.1 p hp,smul_add,smul_add]
    calc
      _=(a • S p+b • S p)+(a • T N p+b • T M p) := by rw [hS]
      _=_ := by abel
  change a*bellmanExtension E F ell L (S p+T N p) p+b*bellmanExtension E F ell L (S p+T M p) p ≤
    bellmanExtension E F ell L (S p+T (a • N+b • M) p) p
  rw [harg]
  exact hh

theorem chuGlobalOperator_matrix_sub_le {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta)
    {p : Point n} (hp : p ∈ backward 1) (H J : Sym n) :
    |chuGlobalOperator E F S T ell L H p-chuGlobalOperator E F S T ell L J p| ≤
      (bellmanMatrixConstant n L*chuTransformNormConstant n K)*‖H-J‖ := by
  have hh := bellmanExtension_matrix_sub_le hEc hne hell hL (chu_matrix_continuousOn hF hp)
    (S p+T H p) (S p+T J p)
  have he : (S p+T H p)-(S p+T J p)=T (H-J) p := by
    have ht := (chuTransformLinear hT p hp).map_sub H J
    change T (H-J) p=T H p-T J p at ht
    rw [ht]
    abel
  rw [he] at hh
  have ht := mul_le_mul_of_nonneg_left (chuTransform_norm_le hK hT hp (H-J))
    (bellmanMatrixConstant_nonneg n (hell.trans hL))
  change |bellmanExtension E F ell L (S p+T H p) p-bellmanExtension E F ell L (S p+T J p) p| ≤ _
  exact hh.trans (by simpa only [bellmanMatrixConstant,mul_assoc] using ht)

def chuGlobalTimeConstant (n : ℕ) (L K : ℝ) : ℝ := K*(2*bellmanMatrixConstant n L+1)

theorem chuGlobalOperator_time_holder {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    (H : Sym n) {p q : Point n} (hp : p ∈ backward 1) (hq : q ∈ backward 1) :
    |chuGlobalOperator E F S T ell L H p-chuGlobalOperator E F S T ell L H q| ≤
      chuGlobalTimeConstant n L K*(1+‖H‖)*holderWeight beta p q := by
  have hCL := bellmanMatrixConstant_nonneg n (hell.trans hL)
  have hW : 0 ≤ holderWeight beta p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hh := bellmanExtension_matrix_sub_le hEc hne hell hL (chu_matrix_continuousOn hF hp)
    (S p+T H p) (S q+T H q)
  have ht := bellmanExtension_time_holder hEc hne hell hL hF (S q+T H q) hp hq
  have hsum := abs_sub_le (bellmanExtension E F ell L (S p+T H p) p)
    (bellmanExtension E F ell L (S q+T H q) p) (bellmanExtension E F ell L (S q+T H q) q)
  have hnorm : ‖(S p+T H p)-(S q+T H q)‖ ≤
      K*holderWeight beta p q+2*K*‖H‖*holderWeight beta p q := by
    have he : (S p+T H p)-(S q+T H q)=(S p-S q)+(T H p-T H q) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (hS.2 p hp q hq) (chuTransform_variation hT H p hp q hq))
  have hmult := mul_le_mul_of_nonneg_left hnorm hCL
  have hremain := mul_nonneg (mul_nonneg hK hW) (add_nonneg hCL (norm_nonneg H))
  change |bellmanExtension E F ell L (S p+T H p) p-bellmanExtension E F ell L (S q+T H q) q| ≤ _
  change |bellmanExtension E F ell L (S p+T H p) p-bellmanExtension E F ell L (S q+T H q) p| ≤
    bellmanMatrixConstant n L*‖(S p+T H p)-(S q+T H q)‖ at hh
  unfold chuGlobalTimeConstant
  nlinarith only [hsum,hh,ht,hmult,hremain]

end Yau.LeafProofs.L05Aux
