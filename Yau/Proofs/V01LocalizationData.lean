import Yau.Proofs.V01WallProfiles

/-! The preliminary localization data retain the supplied flow and original
chart. The actual strict cylinder is then inserted by its native construction. -/

noncomputable section
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

def localizationData
    (o : Pt X) (h : Flow X) (U P ρ Q : STF X) (ρs : ℕ → STF X)
    (u : Pt X → ℝ) (A : ℕ → ℝ)
    (G : CotangentPoint X.manifold → ComplexVector q)
    (T : ℝ) (x : Pt X) (z η : ComplexVector n) (s : ℝ) : VariationData X q :=
  { o := o
    h := h
    U := U
    P := P
    rho := ρ
    Q := Q
    rhoTail := ρs
    u := u
    A := A
    B := fun j => (j : ℝ) + 1
    profileBase := wallProfile 3
    profileFiber := wallProfile 2
    G := G
    T := T
    extendedT := T + 1
    chart := x
    cylinderCenter := (z, η)
    cylinderRadius := 0
    cylinderTimeLo := s
    cylinderTimeHi := s
    contact := ((z, η), s)
    test := fun _ _ => 0 }

end Yau.Blueprint.V01Proof
