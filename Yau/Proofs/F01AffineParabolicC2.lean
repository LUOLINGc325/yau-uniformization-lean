import Yau.Proofs.F01AffineParabolicSpatialJets

/-! The actual parabolic C2 predicate pulls back through affine
parabolic cylinders. The within-time chain rule applies at both closed
faces, so this also transports genuine initial-surface estimates. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem affineParabolicPullback_time_jet {S O : Set (Space n)}
    {l r a b ρ τ : ℝ} {c : Space n} {u : Point n → ℝ}
    (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    {p : Point n} (hp : p ∈ cylinder O a b) :
    HasDerivWithinAt (fun t => affineParabolicPullback ρ c τ u (p.1, t))
      (ρ ^ 2 * timeD (cylinder S l r) u (affineParabolicPoint ρ c τ p)) (Icc a b) p.2 := by
  let q := affineParabolicPoint ρ c τ p
  have hq : q ∈ cylinder S l r := ⟨hSpace hp.1, hClock hp.2⟩
  have hSet : {t : ℝ | (q.1, t) ∈ cylinder S l r} = Icc l r := by
    ext t
    simp only [cylinder, mem_prod, hq.1, true_and, Set.mem_ofPred_eq]
  have hder : HasDerivWithinAt (fun t => u (q.1, t))
      (timeD (cylinder S l r) u q) (Icc l r) q.2 := by
    simpa only [timeD, hSet] using (hu.2.2.2.2.2 q hq).hasDerivWithinAt
  have harg : HasDerivWithinAt (fun t : ℝ => τ + ρ ^ 2 * t) (ρ ^ 2) (Icc a b) p.2 :=
    by simpa only [id_eq, mul_one] using
      (((hasDerivAt_id p.2).const_mul (ρ ^ 2)).const_add τ).hasDerivWithinAt
  have hd := hder.comp p.2 harg hClock
  convert! hd using 1 <;> ring

theorem timeD_affineParabolicPullback {S O : Set (Space n)}
    {l r a b ρ τ : ℝ} {c : Space n} {u : Point n → ℝ}
    (hab : a < b) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    {p : Point n} (hp : p ∈ cylinder O a b) :
    timeD (cylinder O a b) (affineParabolicPullback ρ c τ u) p =
      ρ ^ 2 * timeD (cylinder S l r) u (affineParabolicPoint ρ c τ p) := by
  have hSet : {t : ℝ | (p.1, t) ∈ cylinder O a b} = Icc a b := by
    ext t
    simp only [cylinder, mem_prod, hp.1, true_and, Set.mem_ofPred_eq]
  simpa only [timeD, hSet] using
    (affineParabolicPullback_time_jet hu hSpace hClock hp).derivWithin
      (uniqueDiffOn_Icc hab p.2 hp.2)

theorem c2_affineParabolicPullback {S O : Set (Space n)}
    {l r a b ρ τ : ℝ} {c : Space n} {u : Point n → ℝ}
    (hab : a < b) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r)) :
    C2 (cylinder O a b) (affineParabolicPullback ρ c τ u) := by
  have hMap : MapsTo (affineParabolicPoint ρ c τ) (cylinder O a b) (cylinder S l r) :=
    fun p hp => ⟨hSpace hp.1, hClock hp.2⟩
  have hCont : ContinuousOn (affineParabolicPoint ρ c τ) (cylinder O a b) :=
    (affineParabolicPoint_continuous ρ c τ).continuousOn
  refine ⟨hu.1.comp hCont hMap, ?_, ?_, ?_, ?_, ?_⟩
  · apply ((hu.2.1.comp hCont hMap).const_smul ρ).congr
    intro p hp
    exact spatialD_affineParabolicPullback ρ c τ u p
  · apply ((hu.2.2.1.comp hCont hMap).const_smul (ρ ^ 2)).congr
    intro p hp
    exact spatialDD_affineParabolicPullback ρ c τ u p
  · apply ((hu.2.2.2.1.comp hCont hMap).const_mul (ρ ^ 2)).congr
    intro p hp
    exact timeD_affineParabolicPullback hab hu hSpace hClock hp
  · intro p hp
    have hCurve : ContDiffAt ℝ 2 (fun x : Space n => ρ • x + c) p.1 := by fun_prop
    change ContDiffAt ℝ 2 (fun x : Space n => u (ρ • x + c, τ + ρ ^ 2 * p.2)) p.1
    have hs : ContDiffAt ℝ 2 (fun y : Space n => u (y, τ + ρ ^ 2 * p.2)) (ρ • p.1 + c) :=
      hu.2.2.2.2.1 _ (hMap hp)
    have hcomp := hs.comp p.1 hCurve
    exact hcomp
  · intro p hp
    have hSet : {t : ℝ | (p.1, t) ∈ cylinder O a b} = Icc a b := by
      ext t
      simp only [cylinder, mem_prod, hp.1, true_and, Set.mem_ofPred_eq]
    simpa only [hSet] using
      (affineParabolicPullback_time_jet hu hSpace hClock hp).differentiableWithinAt

end Yau.NodeProofs.F01Aux
