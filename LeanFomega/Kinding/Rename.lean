
import LeanFomega.Typing
open LeanSubst

namespace LeanFomega

structure KindingRen (r : Ren) (Δ1 Δ2 : List Kind) where
  act : ∀ {x T}, Δ1[x]? = some T -> Δ2[r.act x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => KindingRen r Γ Δ

theorem KindingRen.lift A : Δ1 -⟨r⟩> Δ2 -> A::Δ1 -⟨r.lift⟩> A::Δ2 := sorry

theorem KindingRen.id X : X -⟨.id⟩> X := sorry

theorem KindingRen.succ : X -⟨Ren.add 1⟩> A::X := sorry

theorem KindingRen.comp : A -⟨r1⟩> B -> B -⟨r2⟩> C -> A -⟨r1 ∘ r2⟩> C := sorry

def Kinding.rename (m : Δ1 -⟨r⟩> Δ2) : Δ1 ⊢ₖ A : K -> Δ2 ⊢ₖ A⟨r⟩ : K := sorry

end LeanFomega
