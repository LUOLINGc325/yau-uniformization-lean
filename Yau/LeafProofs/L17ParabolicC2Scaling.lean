import Yau.LeafProofs.L17ParabolicScaling

/-! Parabolic C2 and the actual closed-slab time derivative survive the exact rescaling. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

variable {n : ℕ}

def parabolicScalePoint (ρ : ℝ) (p : Point n) : Point n :=
  (ρ⁻¹ • p.1, (ρ ^ 2)⁻¹ * p.2)

theorem parabolicScalePoint_continuous (ρ : ℝ) :
    Continuous (parabolicScalePoint (n := n) ρ) := by
  unfold parabolicScalePoint
  fun_prop

theorem parabolicScalePoint_mem_cylinder {ρ T : ℝ} (hρ : ρ ≠ 0)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    parabolicScalePoint ρ p ∈ cylinder Set.univ 0 (T / ρ ^ 2) :=
  ⟨Set.mem_univ _, parabolic_timeScale_mem_Icc hρ hp.2⟩

theorem parabolicUnscale_time_jet {ρ T : ℝ} (hρ : ρ ≠ 0) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 (T / ρ ^ 2)) u)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    HasDerivWithinAt (fun tau => parabolicUnscale ρ u (p.1, tau))
      (timeD (cylinder Set.univ 0 (T / ρ ^ 2)) u (parabolicScalePoint ρ p))
      (Icc (0 : ℝ) T) p.2 := by
  have hscaled := parabolicScalePoint_mem_cylinder hρ hp
  have hDiff := hu.2.2.2.2.2 (parabolicScalePoint ρ p) hscaled
  have hset : {tau : ℝ | ((parabolicScalePoint ρ p).1, tau) ∈
      cylinder Set.univ 0 (T / ρ ^ 2)} = Icc (0 : ℝ) (T / ρ ^ 2) := by
    ext tau
    simp only [cylinder, mem_prod, mem_univ, true_and, Set.mem_ofPred_eq]
  have hder : HasDerivWithinAt (fun tau => u (ρ⁻¹ • p.1, tau))
      (timeD (cylinder Set.univ 0 (T / ρ ^ 2)) u (parabolicScalePoint ρ p))
      (Icc (0 : ℝ) (T / ρ ^ 2)) ((ρ ^ 2)⁻¹ * p.2) := by
    convert! hDiff.hasDerivWithinAt using 1
    simp [parabolicScalePoint, cylinder]
    ext tau
    rfl
  exact parabolicUnscale_hasDerivWithinAt hρ u p.1 hder

theorem timeD_parabolicUnscale {ρ T : ℝ} (hρ : ρ ≠ 0) (hT : 0 < T) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 (T / ρ ^ 2)) u)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    timeD (cylinder Set.univ 0 T) (parabolicUnscale ρ u) p =
      timeD (cylinder Set.univ 0 (T / ρ ^ 2)) u (parabolicScalePoint ρ p) := by
  have hset : {tau : ℝ | (p.1, tau) ∈ cylinder Set.univ 0 T} = Icc (0 : ℝ) T := by
    ext tau
    simp only [cylinder, mem_prod, mem_univ, true_and, Set.mem_ofPred_eq]
  simp only [timeD, hset]
  exact (parabolicUnscale_time_jet hρ hu hp).derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)

theorem c2_parabolicUnscale {ρ T : ℝ} (hρ : ρ ≠ 0) (hT : 0 < T) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 (T / ρ ^ 2)) u) :
    C2 (cylinder Set.univ 0 T) (parabolicUnscale ρ u) := by
  have hmap : MapsTo (parabolicScalePoint (n := n) ρ) (cylinder Set.univ 0 T)
      (cylinder Set.univ 0 (T / ρ ^ 2)) := fun _ hp => parabolicScalePoint_mem_cylinder hρ hp
  have hcont : ContinuousOn (parabolicScalePoint (n := n) ρ) (cylinder Set.univ 0 T) :=
    (parabolicScalePoint_continuous (n := n) ρ).continuousOn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hu.1.comp hcont hmap).const_mul (ρ ^ 2)
  · apply ((hu.2.1.comp hcont hmap).const_smul ρ).congr
    intro p _
    exact spatialD_parabolicUnscale hρ u p
  · apply (hu.2.2.1.comp hcont hmap).congr
    intro p _
    exact spatialDD_parabolicUnscale hρ u p
  · apply (hu.2.2.2.1.comp hcont hmap).congr
    intro p hp
    exact timeD_parabolicUnscale hρ hT hu hp
  · intro p hp
    have hspace := hu.2.2.2.2.1 (parabolicScalePoint ρ p) (hmap hp)
    change ContDiffAt ℝ 2 (fun x : Space n => ρ ^ 2 *
      u (ρ⁻¹ • x, (ρ ^ 2)⁻¹ * p.2)) p.1
    have hspace' : ContDiffAt ℝ 2 (fun x : Space n => u (x, (ρ ^ 2)⁻¹ * p.2))
        (ρ⁻¹ • p.1) := hspace
    have harg : ContDiffAt ℝ 2 (fun x : Space n => ρ⁻¹ • x) p.1 := by fun_prop
    have hcomp : ContDiffAt ℝ 2
        (fun x : Space n => u (ρ⁻¹ • x, (ρ ^ 2)⁻¹ * p.2)) p.1 := hspace'.comp p.1 harg
    exact contDiffAt_const.mul hcomp
  · intro p hp
    have hset : {tau : ℝ | (p.1, tau) ∈ cylinder Set.univ 0 T} = Icc (0 : ℝ) T := by
      ext tau
      simp only [cylinder, mem_prod, mem_univ, true_and, Set.mem_ofPred_eq]
    simpa only [hset] using (parabolicUnscale_time_jet hρ hu hp).differentiableWithinAt

end Yau.LeafProofs.L17Aux
