import Yau.Proofs.F01PotentialDifferenceHeat
import Yau.Proofs.F01BoundedMaximum
import Yau.LeafProofs.L17HermitianMatrixAssembly

/-! Two actual bounded potential solutions with a common initial value
coincide on the full original closed slab. The scalar maximum principle uses
the actual proper penalty and the actual two flow Laplacians. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem bounded_potential_solutions_unique
    (α : HermitianField M) (h k : ℝ → HermitianField M)
    (U V : M.Carrier → ℝ → ℝ) {T A B Bh Bk : ℝ} (hT : 0 < T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hV : SmoothSpaceTime V (Icc 0 T))
    (hinit : ∀ x, U x 0 = V x 0)
    (hpotU : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpotV : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (k s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => V y s) x)
    (hpdeU : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (hpdeV : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (V x)
      (flowLogDetRatio α k x s) (Icc 0 T) s)
    (hUbound : ∀ x t, t ∈ Icc 0 T → |U x t| ≤ A)
    (hVbound : ∀ x t, t ∈ Icc 0 T → |V x t| ≤ B)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hf0 : ∀ x, 0 ≤ f x)
    (hproper : ∀ b : ℝ, IsCompact {x | f x ≤ b})
    (hLapH : ∀ x t, t ∈ Icc 0 T → laplacian (h t) f x ≤ Bh)
    (hLapK : ∀ x t, t ∈ Icc 0 T → laplacian (k t) f x ≤ Bk) :
    (∀ x t, t ∈ Icc 0 T → U x t = V x t) ∧ ∀ t ∈ Icc 0 T, h t = k t := by
  have hUVsmooth : SmoothSpaceTime (fun x t => U x t - V x t) (Icc 0 T) :=
    fun a => (hU a).sub (hV a)
  have hVUsmooth : SmoothSpaceTime (fun x t => V x t - U x t) (Icc 0 T) :=
    fun a => (hV a).sub (hU a)
  have hUVbound (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) : U x t - V x t ≤ A + B := by
    linarith [hUbound x t ht, hVbound x t ht, le_abs_self (U x t), neg_le_abs (V x t)]
  have hVUbound (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) : V x t - U x t ≤ A + B := by
    linarith [hUbound x t ht, hVbound x t ht, neg_le_abs (U x t), le_abs_self (V x t)]
  have hUV := bounded_subcaloric_nonpos k (fun x t => U x t - V x t) hT hUVsmooth
    (fun x => by rw [hinit x]; simp) hUVbound f hf hf0 hproper hLapK
    (fun x t ht => potential_difference_subcaloric α h k U V hT hU hV hpotU hpotV hpdeU hpdeV
      x t ⟨ht.1.le, ht.2⟩)
  have hVU := bounded_subcaloric_nonpos h (fun x t => V x t - U x t) hT hVUsmooth
    (fun x => by rw [hinit x]; simp) hVUbound f hf hf0 hproper hLapH
    (fun x t ht => potential_difference_subcaloric α k h V U hT hV hU hpotV hpotU hpdeV hpdeU
      x t ⟨ht.1.le, ht.2⟩)
  have heq (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) : U x t = V x t :=
    le_antisymm (sub_nonpos.mp (hUV x t ht)) (sub_nonpos.mp (hVU x t ht))
  refine ⟨heq, ?_⟩
  intro t ht
  apply Yau.LeafProofs.L17HermitianMatrixAssemblyAux.hermitianField_ext
  intro x
  rw [hpotU t ht x, hpotV t ht x]
  have heqSlice : (fun y => U y t) = (fun y => V y t) := funext (fun y => heq y t ht)
  rw [heqSlice]

end Yau.NodeProofs.F01Aux
