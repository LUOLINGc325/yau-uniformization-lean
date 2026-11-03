import Yau.LeafProofs.L05MongeWrapper

namespace Yau.LeafProofs.L05Aux

theorem leaf_of_chu (hChu : Yau.ParabolicCandidates.ChuTransformedHessian) :
    Yau.LeafObligations.L05 :=
  ⟨hChu,complexHessianRepresentation,mongeAmpereInitialSchauder_of_chu hChu⟩

end Yau.LeafProofs.L05Aux
