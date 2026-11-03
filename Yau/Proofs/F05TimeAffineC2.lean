import Yau.Proofs.F05BootstrapRestrictions

/-! Actual affine changes of time preserve the closed-slab parabolic jets.
The derivative at each end is taken within the stated interval. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05TimeAffinePoint (a b : ℝ) (p : Point n) : Point n := (p.1,a*p.2+b)

def F05TimeAffine {E : Type*} (a b : ℝ) (u : Point n → E) : Point n → E :=
  fun p => u (F05TimeAffinePoint a b p)

theorem F05_timeAffine_hasDerivWithinAt {X : Set (Space n)} {l r L R a b : ℝ}
    (hMap : MapsTo (fun t : ℝ => a*t+b) (Icc l r) (Icc L R))
    {u : Point n → ℝ} {p : Point n}
    (hu : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Icc L R) (a*p.2+b)) :
    HasDerivWithinAt (fun t => F05TimeAffine a b u (p.1,t))
      (a*derivWithin (fun t => u (p.1,t)) (Icc L R) (a*p.2+b)) (Icc l r) p.2 := by
  have h := hu.hasDerivWithinAt.comp p.2
    (((hasDerivAt_id p.2).const_mul a).add_const b).hasDerivWithinAt hMap
  convert! h using 1
  simp only [mul_one,mul_comm]

theorem F05_timeD_timeAffine {X : Set (Space n)} {l r L R a b : ℝ}
    (hlr : l < r) (hMap : MapsTo (fun t : ℝ => a*t+b) (Icc l r) (Icc L R))
    {u : Point n → ℝ} (hu : C2 (cylinder X L R) u)
    {p : Point n} (hp : p ∈ cylinder X l r) :
    timeD (cylinder X l r) (F05TimeAffine a b u) p =
      a*timeD (cylinder X L R) u (F05TimeAffinePoint a b p) := by
  have hpBig : F05TimeAffinePoint a b p ∈ cylinder X L R := ⟨hp.1,hMap hp.2⟩
  have hU : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Icc L R) (a*p.2+b) := by
    simpa only [F05TimeAffinePoint,cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq]
      using hu.2.2.2.2.2 _ hpBig
  have h := (F05_timeAffine_hasDerivWithinAt (X := X) hMap hU).derivWithin
    (uniqueDiffOn_Icc hlr _ hp.2)
  simpa only [timeD,F05TimeAffinePoint,cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq] using h

theorem F05_c2_timeAffine {X : Set (Space n)} {l r L R a b : ℝ}
    (hlr : l < r) (hMap : MapsTo (fun t : ℝ => a*t+b) (Icc l r) (Icc L R))
    {u : Point n → ℝ} (hu : C2 (cylinder X L R) u) :
    C2 (cylinder X l r) (F05TimeAffine a b u) := by
  have hMapQ : MapsTo (F05TimeAffinePoint a b) (cylinder X l r) (cylinder X L R) :=
    fun _ hp => ⟨hp.1,hMap hp.2⟩
  have hCont : ContinuousOn (F05TimeAffinePoint (n := n) a b) (cylinder X l r) :=
    (continuous_fst.prodMk ((continuous_const.mul continuous_snd).add continuous_const)).continuousOn
  refine ⟨hu.1.comp hCont hMapQ,hu.2.1.comp hCont hMapQ,
    hu.2.2.1.comp hCont hMapQ,?_,?_,?_⟩
  · exact (continuousOn_const.mul (hu.2.2.2.1.comp hCont hMapQ)).congr
      (fun p hp => F05_timeD_timeAffine hlr hMap hu hp)
  · intro p hp
    exact hu.2.2.2.2.1 _ (hMapQ hp)
  · intro p hp
    have hU : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Icc L R) (a*p.2+b) := by
      simpa only [F05TimeAffinePoint,cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq]
        using hu.2.2.2.2.2 _ (hMapQ hp)
    simpa only [cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq]
      using (F05_timeAffine_hasDerivWithinAt (X := X) hMap hU).differentiableWithinAt

end Yau.Proofs.F05Aux
