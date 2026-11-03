import Yau.LeafProofs.L17GaussianParametrixFunction

/-! Actual one-sided time jets of the Gaussian parametrix, including both endpoints. -/

open Set Metric
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem c2_restricted_time_hasDerivWithinAt {T : ℝ} (hT : 0 ≤ T)
    {u : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 T) u)
    (z : Space n) (t : Time T) :
    HasDerivWithinAt (fun τ => u (z,(projIcc (0 : ℝ) T hT τ : ℝ)))
      (timeD (cylinder Set.univ 0 T) u (z,(t : ℝ))) (Icc (0 : ℝ) T) (t : ℝ) := by
  have hraw : HasDerivWithinAt (fun τ => u (z,τ))
      (timeD (cylinder Set.univ 0 T) u (z,(t : ℝ))) (Icc (0 : ℝ) T) (t : ℝ) := by
    convert! (hu.2.2.2.2.2 (z,(t : ℝ)) ⟨mem_univ _,t.property⟩).hasDerivWithinAt using 1
    ext τ
    simp only [cylinder,mem_prod,mem_univ,true_and,Set.mem_ofPred_eq]
  apply hraw.congr_of_mem _ t.property
  intro τ hτ
  rw [projIcc_of_mem _ hτ]

def gaussianTimeTerm (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) : Cylinder M T → ℝ :=
  localizedTerm P T p (fun q => timeD (cylinder Set.univ 0 T)
    (localGaussian P T hT f p) (q.1,(q.2 : ℝ)))

theorem gaussianTerm_hasDerivWithinAt (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers)
    (hu : C2 (cylinder Set.univ 0 T) (localGaussian P T hT f p))
    (x : M.Carrier) (t : Time T) :
    HasDerivWithinAt (fun τ => gaussianTerm P T hT f p (x,projIcc (0 : ℝ) T hT τ))
      (gaussianTimeTerm P T hT f p (x,t)) (Icc (0 : ℝ) T) (t : ℝ) := by
  apply localizedTerm_hasDerivWithinAt
  intro z _ s
  exact c2_restricted_time_hasDerivWithinAt hT hu z s

theorem gaussianParametrixFun_hasDerivWithinAt (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ)
    (hu : ∀ p, C2 (cylinder Set.univ 0 T) (localGaussian P T hT f p))
    (x : M.Carrier) (t : Time T) :
    HasDerivWithinAt (fun τ => gaussianParametrixFun P T hT f (x,projIcc (0 : ℝ) T hT τ))
      (∑ᶠ p,gaussianTimeTerm P T hT f p (x,t)) (Icc (0 : ℝ) T) (t : ℝ) := by
  apply globalSum_hasDerivWithinAt
  intro p z _ s
  exact c2_restricted_time_hasDerivWithinAt hT (hu p) z s

end Yau.LeafProofs.L17Aux
