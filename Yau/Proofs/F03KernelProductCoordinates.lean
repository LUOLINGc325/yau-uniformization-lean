import Yau.Proofs.F03KernelChartEquation

/-! Actual real linear product coordinates for both kernel variables and time. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def kernelPairPackLinearEquiv (n : ℕ) :
    (ComplexVector n × ComplexVector n) ≃ₗ[ℝ] ComplexVector (n+n) where
  toFun p := WithLp.toLp 2 (Fin.append (fun i => p.1 i) (fun i => p.2 i))
  invFun z := (WithLp.toLp 2 (fun i => z (Fin.castAdd n i)),
    WithLp.toLp 2 (fun i => z (Fin.natAdd n i)))
  left_inv p := by
    apply Prod.ext
    · ext i
      exact Fin.append_left _ _ i
    · ext i
      exact Fin.append_right _ _ i
  right_inv z := by
    ext i
    exact congrFun (Fin.append_castAdd_natAdd (f := (fun i => z i))) i
  map_add' p q := by
    ext i
    change Fin.append (fun j => p.1 j+q.1 j) (fun j => p.2 j+q.2 j) i=
      Fin.append (fun j => p.1 j) (fun j => p.2 j) i+Fin.append (fun j => q.1 j) (fun j => q.2 j) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left,Fin.append_right]
  map_smul' c p := by
    ext i
    change Fin.append (fun j => c • p.1 j) (fun j => c • p.2 j) i=
      c • Fin.append (fun j => p.1 j) (fun j => p.2 j) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left,Fin.append_right]

def kernelPairPack (n : ℕ) :
    (ComplexVector n × ComplexVector n) ≃L[ℝ] ComplexVector (n+n) :=
  (kernelPairPackLinearEquiv n).toContinuousLinearEquiv

theorem kernelPairPack_apply (n : ℕ) (p : ComplexVector n × ComplexVector n) (i : Fin (n+n)) :
    kernelPairPack n p i=Fin.append (fun j => p.1 j) (fun j => p.2 j) i := rfl

theorem kernelPairPack_symm_fst_apply (n : ℕ) (z : ComplexVector (n+n)) (i : Fin n) :
    ((kernelPairPack n).symm z).1 i=z (Fin.castAdd n i) := rfl

theorem kernelPairPack_symm_snd_apply (n : ℕ) (z : ComplexVector (n+n)) (i : Fin n) :
    ((kernelPairPack n).symm z).2 i=z (Fin.natAdd n i) := rfl

def kernelPairTimePack (n : ℕ) :
    ((ComplexVector n × ComplexVector n) × ℝ) ≃L[ℝ] Point (n+n) :=
  (kernelPairPack n).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

def kernelRealIndexLeft (n : ℕ) (i : RIdx n) : RIdx (n+n) := (Fin.castAdd n i.1,i.2)
def kernelRealIndexRight (n : ℕ) (i : RIdx n) : RIdx (n+n) := (Fin.natAdd n i.1,i.2)

theorem fin_castAdd_ne_natAdd (n : ℕ) (i j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n j := by
  intro h
  have hh : i.val=n+j.val := congrArg Fin.val h
  omega

theorem kernelPairPack_symm_realVec_left (n : ℕ) (i : RIdx n) :
    (kernelPairPack n).symm (realVec (kernelRealIndexLeft n i))=(realVec i,0) := by
  apply Prod.ext
  · ext j
    simp only [kernelPairPack_symm_fst_apply,kernelRealIndexLeft,realVec,
      PiLp.smul_apply,PiLp.single_apply,Fin.castAdd_inj]
  · ext j
    have hne := fin_castAdd_ne_natAdd n i.1 j
    change ((if i.2=0 then (1 : ℂ) else Complex.I) •
      EuclideanSpace.single (Fin.castAdd n i.1) 1) (Fin.natAdd n j)=0
    rw [PiLp.smul_apply,PiLp.single_apply,if_neg hne.symm,smul_zero]

theorem kernelPairPack_symm_realVec_right (n : ℕ) (i : RIdx n) :
    (kernelPairPack n).symm (realVec (kernelRealIndexRight n i))=(0,realVec i) := by
  apply Prod.ext
  · ext j
    have hne := fin_castAdd_ne_natAdd n j i.1
    change ((if i.2=0 then (1 : ℂ) else Complex.I) •
      EuclideanSpace.single (Fin.natAdd n i.1) 1) (Fin.castAdd n j)=0
    rw [PiLp.smul_apply,PiLp.single_apply,if_neg hne,smul_zero]
  · ext j
    simp only [kernelPairPack_symm_snd_apply,kernelRealIndexRight,realVec,
      PiLp.smul_apply,PiLp.single_apply,Fin.natAdd_inj]

end Yau.Proofs.F03Aux
