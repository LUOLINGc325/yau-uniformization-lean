import Yau.LeafProofs.L23CovariantTrace
import Yau.LeafProofs.L23CovariantPermutation

/-! The full-rank rough-Laplacian commutator before the contracted Bianchi
simplification. Every pre-existing derivative slot participates. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem cons_comp_swap_firstTwo {ι : Type*} {r : ℕ}
    (a b : ι) (v : Fin r → ι) :
    (Fin.cons a (Fin.cons b v)) ∘ Equiv.swap (0 : Fin (r+2)) 1=
      Fin.cons b (Fin.cons a v) := by
  classical
  funext s
  refine Fin.cases ?_ (fun s => Fin.cases ?_ (fun j => ?_) s) s
  · simp [Function.comp_def,Equiv.swap_apply_def]
  · simp [Function.comp_def,Equiv.swap_apply_def]
  · have h0 : j.succ.succ ≠ (0 : Fin (r+2)) := Fin.succ_ne_zero _
    have h1 : j.succ.succ ≠ (1 : Fin (r+2)) := by
      intro hh
      have he : j.succ=(0 : Fin (r+1)) := Fin.succ_inj.mp hh
      exact Fin.succ_ne_zero _ he
    simp [Function.comp_def,Equiv.swap_apply_def,h0,h1]

variable {n r : ℕ} {M : ComplexManifold n}

def curvatureActionField (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n) : CovTensor n (r+2) :=
  fun v => curvatureAction h c z (v 0) (v 1) (A z) (fun j => v j.succ.succ)

theorem curvatureActionField_eq_commutator (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    curvatureActionField h c A z=
      (fun v => covariantD h c (covariantD h c A) z v-
        covariantD h c (covariantD h c A) z (v ∘ Equiv.swap (0 : Fin (r+2)) 1)) := by
  funext v
  let u : Fin r → RIdx n := fun j => v j.succ.succ
  have hv : Fin.cons (v 0) (Fin.cons (v 1) u)=v := by
    funext s
    refine Fin.cases ?_ (fun s => Fin.cases ?_ (fun j => ?_) s) s <;> rfl
  have hp : Fin.cons (v 1) (Fin.cons (v 0) u)=
      v ∘ Equiv.swap (0 : Fin (r+2)) 1 := by
    calc
      _=(Fin.cons (v 0) (Fin.cons (v 1) u)) ∘ Equiv.swap (0 : Fin (r+2)) 1 :=
        (cons_comp_swap_firstTwo _ _ _).symm
      _=_ := by rw [hv]
  have hc := covariantD_commutator h hh c A hA hz (v 0) (v 1) u
  rw [hv,hp] at hc
  exact hc.symm

theorem covariantD_curvatureActionField_cons (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i b : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (curvatureActionField h c A) z (Fin.cons a (Fin.cons i (Fin.cons b v)))=
      covariantD h c (covariantD h c (covariantD h c A)) z
        (Fin.cons a (Fin.cons i (Fin.cons b v)))-
      covariantD h c (covariantD h c (covariantD h c A)) z
        (Fin.cons a (Fin.cons b (Fin.cons i v))) := by
  let B := covariantD h c (covariantD h c A)
  let e := Equiv.swap (0 : Fin (r+2)) 1
  have hEq : curvatureActionField h c A=ᶠ[𝓝 z]
      (fun w v => B w v-B w (v ∘ e)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    exact curvatureActionField_eq_commutator h hh c A hA hw
  have hBs (u : Fin (r+2) → RIdx n) := ((covariantD_contDiffOn h hh c (covariantD h c A)
    (covariantD_contDiffOn h hh c A hA) u).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hCs (u : Fin (r+2) → RIdx n) :
      DifferentiableAt ℝ (fun w => B w (u ∘ e)) z := hBs (u ∘ e)
  have hd := covariantD_eventuallyEq h c _ _ z hEq
  change covariantD h c (curvatureActionField h c A) z=
    covariantD h c (fun w => B w-(fun u => B w (u ∘ e))) z at hd
  rw [covariantD_sub_at h c _ _ z hBs hCs] at hd
  have hp := congrFun hd (Fin.cons a (Fin.cons i (Fin.cons b v)))
  change covariantD h c (curvatureActionField h c A) z (Fin.cons a (Fin.cons i (Fin.cons b v)))=
    covariantD h c B z (Fin.cons a (Fin.cons i (Fin.cons b v)))-
      covariantD h c (fun w u => B w (u ∘ e)) z (Fin.cons a (Fin.cons i (Fin.cons b v))) at hp
  rw [covariantD_permute_cons,cons_comp_swap_firstTwo] at hp
  exact hp

theorem covariantD_roughLap_commutator_raw (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (roughLap h c A) z (Fin.cons i v)-
      roughLap h c (covariantD h c A) z (Fin.cons i v)=
      ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        (curvatureAction h c z i a (covariantD h c A z) (Fin.cons b v)+
          covariantD h c (curvatureActionField h c A) z
            (Fin.cons a (Fin.cons i (Fin.cons b v)))) := by
  have hBs (u : Fin (r+2) → RIdx n) := ((covariantD_contDiffOn h hh c (covariantD h c A)
    (covariantD_contDiffOn h hh c A hA) u).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have ht := covariantD_tensorMetricTrace h hh c (covariantD h c (covariantD h c A)) hz hBs i v
  change covariantD h c (roughLap h c A) z (Fin.cons i v)=
    ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      covariantD h c (covariantD h c (covariantD h c A)) z
        (Fin.cons i (Fin.cons a (Fin.cons b v))) at ht
  rw [ht]
  change (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
    covariantD h c (covariantD h c (covariantD h c A)) z
      (Fin.cons i (Fin.cons a (Fin.cons b v))))-
        (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
          covariantD h c (covariantD h c (covariantD h c A)) z
            (Fin.cons a (Fin.cons b (Fin.cons i v))))=_
  simp only [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [←mul_sub]
  congr 1
  have hc := covariantD_commutator h hh c (covariantD h c A)
    (covariantD_contDiffOn h hh c A hA) hz i a (Fin.cons b v)
  change covariantD h c (covariantD h c (covariantD h c A)) z
      (Fin.cons i (Fin.cons a (Fin.cons b v)))-
    covariantD h c (covariantD h c (covariantD h c A)) z
      (Fin.cons a (Fin.cons i (Fin.cons b v)))=
    curvatureAction h c z i a (covariantD h c A z) (Fin.cons b v) at hc
  have hD := covariantD_curvatureActionField_cons h hh c A hA hz a i b v
  linarith [hc,hD]

end Yau.LeafProofs.L23Aux
